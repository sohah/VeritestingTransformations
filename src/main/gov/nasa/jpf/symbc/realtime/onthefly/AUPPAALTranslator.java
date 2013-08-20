/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.onthefly;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.symbc.realtime.MethodDesc;
import gov.nasa.jpf.symbc.symexectree.SymExecTreeUtils;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;

import java.util.HashMap;
import java.util.List;
import java.util.Stack;

import uppaal.Automaton;
import uppaal.Location;
import uppaal.Location.LocationType;
import uppaal.NTA;
import uppaal.Transition;
import uppaal.labels.Synchronization;
import uppaal.labels.Synchronization.SyncType;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public abstract class AUPPAALTranslator {
	
	protected static final String DEF_OUTPUT_PATH = "./uppaalModel.xml";
	
	private NTA nta;
	private List<MethodDesc> symbolicMethods;
	protected HashMap<MethodDesc, TranslationUnit> methodAutomatonMap;
	
	private Instruction previouslyExecutedInstr;
	protected int unique_id;
	
	protected Config jpfConf;
	protected boolean targetTetaSARTS;
	
	protected AUPPAALTranslator(Config jpfConf, boolean targetTetaSARTS) {
		this.previouslyExecutedInstr = null;
		this.unique_id = 0;
		this.nta = new NTA();
		this.jpfConf = jpfConf;	
		this.targetTetaSARTS = targetTetaSARTS;
		String[] methods = this.jpfConf.getStringArray("symbolic.method");
		this.symbolicMethods = SymExecTreeUtils.convertJPFConfSymbcDescs(methods);
		this.methodAutomatonMap = new HashMap<MethodDesc, TranslationUnit>();
		for(MethodDesc m : this.symbolicMethods) {
			TranslationUnit tu = new TranslationUnit(m, this.targetTetaSARTS);
			this.methodAutomatonMap.put(m, tu);
		}
	}
	
	public NTA finalizeAndGetNTA() {
		for(TranslationUnit tu : this.methodAutomatonMap.values()) {
			this.nta.addAutomaton(tu.getAutomaton());
			if(!targetTetaSARTS) {
				this.nta.getSystemDeclaration().addSystemInstance(tu.getTargetMethod().getShortMethodName());
				this.nta.getDeclarations().add("clock globalClock;");
			}
		}
		return this.nta;
	}
	
	public void finalizeAutomatonConstruction(StackFrame frame) {
		MethodDesc mi = SymExecTreeUtils.getTargetMethodOfFrame(this.symbolicMethods, frame);
		TranslationUnit tu = this.methodAutomatonMap.get(mi);
		constructTransition(this.previouslyExecutedInstr, tu.getPrevLoc(), tu.getFinalLoc(), tu.getAutomaton(), this.targetTetaSARTS);
	}
	
	public void translateInstruction(Instruction instr, StackFrame frame) {
		MethodDesc mi = SymExecTreeUtils.getTargetMethodOfFrame(this.symbolicMethods, frame);
		TranslationUnit tu = this.methodAutomatonMap.get(mi);
		Location nxtLoc = null;
		if(instr instanceof IfInstruction) {
			InstrExecContext instrCtx = new InstrExecContext(instr, frame);
			if(tu.hasIfInstrBeenTranslated(instrCtx)) {
				nxtLoc = tu.getIfInstrLocation(instrCtx);
			} else {
				nxtLoc = constructLocation(instr, tu.getAutomaton(), this.targetTetaSARTS);
				tu.addIfInstrContext(instrCtx, nxtLoc);
			}
		} else {
			nxtLoc = constructLocation(instr, tu.getAutomaton(), this.targetTetaSARTS);
		}
		assert nxtLoc != null;
		
		Transition trans = null;
		if(this.previouslyExecutedInstr == null) { //Must be the first instruction i.e. initLoc -> firstInstrLoc
			trans = new Transition(tu.getAutomaton(), tu.getInitLoc(), nxtLoc);
			if(this.targetTetaSARTS)
				trans.setSync(new Synchronization("run[tID]", SyncType.RECEIVER));
		} else
			trans = constructTransition(this.previouslyExecutedInstr, tu.getPrevLoc(), nxtLoc, tu.getAutomaton(), this.targetTetaSARTS);
		tu.setPrevLoc(trans.getTarget());
		this.previouslyExecutedInstr = instr;
	}
	
	public void addChoice(Instruction instr, StackFrame frame) {
		MethodDesc mi = SymExecTreeUtils.getTargetMethodOfFrame(this.symbolicMethods, frame);
		TranslationUnit tu = this.methodAutomatonMap.get(mi);
		tu.addChoice(instr);
	}
	
	public void backTracked(Instruction instr, StackFrame frame) {
		MethodDesc mi = SymExecTreeUtils.getTargetMethodOfFrame(this.symbolicMethods, frame);
		TranslationUnit tu = this.methodAutomatonMap.get(mi);
		tu.restoreToPrevChoice();
	}
	
	protected abstract Location constructLocation(Instruction instr, Automaton ta, boolean targetTetaSARTS);
	protected abstract Transition constructTransition(Instruction instr, Location prevLoc, Location nxtLoc, Automaton ta, boolean targetTetaSARTS);
	
	protected class TranslationUnit {
		private Stack<Instruction> choices;
		private Location prevLoc;
		private Location initLoc;
		private Location finalLoc;
		
		private Automaton ta;
		private MethodDesc targetMethod;
		
		private HashMap<InstrExecContext, Location> ifInstrToLocMap;
		
		public TranslationUnit(MethodDesc method, boolean targetTetaSARTS) {
			this.targetMethod = method;
			
			this.ta = new Automaton(method.getShortMethodName());
			this.initLoc = this.prevLoc = new Location(ta, "initLoc");
			this.ta.setInit(initLoc);
			this.finalLoc = new Location(ta, "final");
			this.finalLoc.setType(LocationType.COMMITTED);
			this.ta.getDeclaration().add("clock executionTime;");
			if(targetTetaSARTS) {
				this.ta.setParameter("const ThreadID tID");
				Transition finalTrans = new Transition(ta, finalLoc, initLoc);
				finalTrans.setSync(new Synchronization("run[tID]", SyncType.INITIATOR));
			} else {
				this.initLoc.setType(LocationType.COMMITTED);
			}
			this.choices = new Stack<Instruction>();
			this.ifInstrToLocMap = new HashMap<InstrExecContext, Location>();
		}
		
		public boolean hasIfInstrBeenTranslated(InstrExecContext instrCtx) {
			return this.ifInstrToLocMap.containsKey(instrCtx);
		}
		
		public Location getIfInstrLocation(InstrExecContext instrCtx) {
			return this.ifInstrToLocMap.get(instrCtx);
		}
		
		public MethodDesc getTargetMethod() {
			return this.targetMethod;
		}
		
		public Location getPrevLoc() {
			return this.prevLoc;
		}
		
		public Location getFinalLoc() {
			return this.finalLoc;
		}
		
		public Location getInitLoc() {
			return this.initLoc;
		}
		
		public Location setPrevLoc(Location loc) {
			return this.prevLoc = loc;
		}
		
		public void addChoice(Instruction choice) {
			this.choices.add(choice);
		}
		
		public void addIfInstrContext(InstrExecContext ifInstrCtx, Location loc) {
			this.ifInstrToLocMap.put(ifInstrCtx, loc);
		}
		
		public void restoreToPrevChoice() {
			if(this.choices.size() > 0) {
				this.prevLoc = this.ifInstrToLocMap.get(this.choices.pop());
			}
		}
		
		public Automaton getAutomaton() {
			return ta;
		}
	}
	
	private class InstrExecContext {
		private final Instruction instr;
		private final StackFrame frame;

		public InstrExecContext(Instruction instr, StackFrame frame) {
			this.instr = instr;
			this.frame = frame;
		}
		
		public Instruction getInstr() {
			return instr;
		}
		
		public StackFrame getFrame() {
			return frame;
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((frame == null) ? 0 : frame.hashCode());
			result = prime * result + ((instr == null) ? 0 : instr.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			InstrExecContext other = (InstrExecContext) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (frame == null) {
				if (other.frame != null)
					return false;
			} else if (!frame.equals(other.frame))
				return false;
			if (instr == null) {
				if (other.instr != null)
					return false;
			} else if (!instr.equals(other.instr))
				return false;
			return true;
		}

		private AUPPAALTranslator getOuterType() {
			return AUPPAALTranslator.this;
		}
		
	}
}
