/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.onthefly;

import java.util.List;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.symbc.realtime.JOPUtil;
import gov.nasa.jpf.vm.Instruction;
import uppaal.Automaton;
import uppaal.Location;
import uppaal.Transition;
import uppaal.labels.Synchronization;
import uppaal.labels.Synchronization.SyncType;
import uppaal.labels.Update;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class JOPUPPAALTranslator extends AUPPAALTranslator {

	public JOPUPPAALTranslator(Config jpfConf, boolean targetTetaSARTS) {
		super(jpfConf, targetTetaSARTS);
		if(!targetTetaSARTS) {
			for(TranslationUnit tu : super.methodAutomatonMap.values()) {
				tu.getAutomaton().getDeclaration().add("int methodSwitchCost;");
			}
		}
	}

	@Override
	protected Location constructLocation(Instruction instr, Automaton ta, boolean targetTetaSARTS) {
		Location loc = new Location(ta, instr.getMnemonic() + "_" + super.unique_id++);
		StringBuilder invariantBuilder = new StringBuilder();
		invariantBuilder.append("executionTime <= ")
						.append(JOPUtil.getWCET(instr));
		if(targetTetaSARTS) {
			invariantBuilder.append("&&\n")
							.append("executionTime' == running[tID]");
		}
		loc.setInvariant(invariantBuilder.toString());
		StringBuilder commentBuilder = new StringBuilder();
		commentBuilder.append("Location: ")
					  .append(instr.getFileLocation());
		loc.setComment(commentBuilder.toString());
		return loc;
	}

	@Override
	protected Transition constructTransition(Instruction instr, Location prevLoc, Location nxtLoc, Automaton ta, boolean targetTetaSARTS) {
		if(instr instanceof ReturnInstruction) {
			Location methodSwitchLocation = new Location(ta, "mSwitch" + super.unique_id++);
			StringBuilder invariantBuilder = new StringBuilder();
			invariantBuilder.append("executionTime <= ")
							.append("methodSwitchCost");
			if(targetTetaSARTS) {
				invariantBuilder.append("&&\n")
								.append("executionTime' == running[tID]");
			}
			methodSwitchLocation.setInvariant(invariantBuilder.toString());
			Transition retInstrToMSwitchTrans = new Transition(ta, prevLoc, methodSwitchLocation);
			retInstrToMSwitchTrans.addUpdate("executionTime = 0,\nmethodSwitchCost = " + 
														JOPUtil.calculateMethodSwitchCost(false, ((ReturnInstruction)instr).getMethodInfo()));//getReturnFrame().getMethodInfo()));
			retInstrToMSwitchTrans.setGuard("executionTime == " + JOPUtil.getWCET(instr));
			
			Transition switchToNxtLocTrans = new Transition(ta, methodSwitchLocation, nxtLoc);
			switchToNxtLocTrans.setGuard("executionTime == methodSwitchCost");
			switchToNxtLocTrans.addUpdate("executionTime = 0");
			return switchToNxtLocTrans;
			
		} else {
			Transition trans = new Transition(ta, prevLoc, nxtLoc);
			trans.setGuard("executionTime == " + JOPUtil.getWCET(instr));
			trans.addUpdate("executionTime = 0");
			return trans;
		}

	}

}
