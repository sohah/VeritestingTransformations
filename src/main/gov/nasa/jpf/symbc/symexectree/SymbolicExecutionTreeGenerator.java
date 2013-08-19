/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Stack;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.symbc.realtime.MethodDesc;
import gov.nasa.jpf.symbc.realtime.RealTimeUtils;
import gov.nasa.jpf.vm.Instruction;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SymbolicExecutionTreeGenerator {

	private Config jpfConf;
	private NodeFactory nodeFactory;
	
	private Instruction previouslyExecutedInstr;
	private SymbolicExecutionTree tree;
	private LinkedList<MethodDesc> symbolicMethods;
	private HashMap<MethodDesc, TranslationUnit> methTUMap;
	
	public SymbolicExecutionTreeGenerator(Config jpfConf, NodeFactory nodeFactory) {
		this.jpfConf = jpfConf;
		this.nodeFactory = nodeFactory;
		
		this.previouslyExecutedInstr = null;
		
		String[] methods = this.jpfConf.getStringArray("symbolic.method");
		this.symbolicMethods = RealTimeUtils.convertJPFConfSymbcDescs(methods);
		this.methTUMap = new HashMap<MethodDesc, TranslationUnit>();
		for(MethodDesc m : this.symbolicMethods) {
			TranslationUnit tu = new TranslationUnit(m);
			this.methTUMap.put(m, tu);
		}
	}
	
	public void build(InstrContext instrCtx) {
		MethodDesc mi = RealTimeUtils.getTargetMethodOfFrame(this.symbolicMethods, instrCtx.getFrame());
		TranslationUnit tu = this.methTUMap.get(mi);
		Node nxtNode = null;
		if(instrCtx.getInstr() instanceof IfInstruction) {
			if(tu.hasIfInstrBeenTranslated(instrCtx)) {
				nxtNode = tu.getIfInstrNode(instrCtx);
			} else {
				nxtNode = this.nodeFactory.constructNode(instrCtx, tu.getSymTree());
				tu.addIfInstrCtx(instrCtx, nxtNode);
			}
		} else {
			nxtNode = this.nodeFactory.constructNode(instrCtx, tu.getSymTree());
		}
		
		if(this.previouslyExecutedInstr != null) {
			new Transition(tu.getPrevNode(), nxtNode, tu.getSymTree());
		}
		tu.setPrevNode(nxtNode);
		
		//TODO: Do we need this one?
		this.previouslyExecutedInstr = instrCtx.getInstr();
	}
	
	public void addChoice(InstrContext instrCtx) {
		MethodDesc mi = RealTimeUtils.getTargetMethodOfFrame(this.symbolicMethods, instrCtx.getFrame());
		TranslationUnit tu = this.methTUMap.get(mi);
		tu.addChoice(instrCtx);
	}
	
	public void restoreChoice(InstrContext instrCtx) {
		MethodDesc mi = RealTimeUtils.getTargetMethodOfFrame(this.symbolicMethods, instrCtx.getFrame());
		TranslationUnit tu = this.methTUMap.get(mi);
		tu.restoreToPrevChoice();
	}
	
	public LinkedList<SymbolicExecutionTree> getTrees() {
		LinkedList<SymbolicExecutionTree> trees = new LinkedList<>();
		for(TranslationUnit tu : this.methTUMap.values())
			trees.add(tu.getSymTree());
		return trees;
	}

	private class TranslationUnit {
		private Stack<InstrContext> choices;
		private SymbolicExecutionTree tree;
		private Node prevNode;
		
		private HashMap<InstrContext, Node> ifInstrToNodeMap;
		
		public TranslationUnit(MethodDesc method) {	
			this.tree = new SymbolicExecutionTree(method);
			this.choices = new Stack<InstrContext>();
			this.ifInstrToNodeMap = new HashMap<InstrContext, Node>();
			this.prevNode = null;
		}
		
		public boolean hasIfInstrBeenTranslated(InstrContext instrCtx) {
			return this.ifInstrToNodeMap.containsKey(instrCtx);
		}
		
		public Node getIfInstrNode(InstrContext instrCtx) {
			return this.ifInstrToNodeMap.get(instrCtx);
		}
		
		public Node getPrevNode() {
			return this.prevNode;
		}
		
		public void setPrevNode(Node node) {
			this.prevNode = node;
		}
		
		public void addChoice(InstrContext choice) {
			this.choices.add(choice);
		}
		
		public void addIfInstrCtx(InstrContext ifInstrCtx, Node node) {
			this.ifInstrToNodeMap.put(ifInstrCtx, node);
		}
		
		public void restoreToPrevChoice() {
			if(this.choices.size() > 0) {
				this.prevNode = this.ifInstrToNodeMap.get(this.choices.pop());
			}
		}
		
		public SymbolicExecutionTree getSymTree() {
			return this.tree;
		}
	}
	
	
}
