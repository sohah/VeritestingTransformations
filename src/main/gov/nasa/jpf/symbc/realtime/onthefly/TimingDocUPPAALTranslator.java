/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.onthefly;

import uppaal.Automaton;
import uppaal.Location;
import uppaal.Transition;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.realtime.TimingDoc;
import gov.nasa.jpf.symbc.realtime.TimingDocGenerator;
import gov.nasa.jpf.vm.Instruction;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TimingDocUPPAALTranslator extends AUPPAALTranslator {

	
	private TimingDoc timingDoc;
	/**
	 * @param jpfConf
	 */
	protected TimingDocUPPAALTranslator(Config jpfConf, String timingDocPath, boolean targetTetaSARTS) {
		super(jpfConf, targetTetaSARTS);
		this.timingDoc = TimingDocGenerator.generate(timingDocPath);
	}

	@Override
	protected Location constructLocation(Instruction instr, Automaton ta, boolean targetTetaSARTS) {
		Location loc = new Location(ta, instr.getMnemonic() + "_" + super.unique_id++);
		StringBuilder invariantBuilder = new StringBuilder();
		invariantBuilder.append("executionTime <= ")
						.append(timingDoc.get(instr.getMnemonic()).getWcet());
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
		Transition trans = new Transition(ta, prevLoc, nxtLoc);
		trans.setGuard("executionTime == " + timingDoc.get(instr.getMnemonic()).getWcet());
		trans.addUpdate("executionTime = 0");
		return trans;
	}

}
