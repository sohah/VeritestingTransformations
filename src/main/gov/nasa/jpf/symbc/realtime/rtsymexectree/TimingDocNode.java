/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

import gov.nasa.jpf.symbc.realtime.InstructionTimingInfo;
import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TimingDocNode extends RTNode implements IHasWCET, IHasBCET {
	
	private InstructionTimingInfo instrTiming;
	
	public TimingDocNode(InstrContext instructionContext, InstructionTimingInfo instrTiming) {
		super(instructionContext);
		this.instrTiming = instrTiming;
	}

	public TimingDocNode(InstrContext instructionContext, SymbolicExecutionTree tree, InstructionTimingInfo instrTiming) {
		super(instructionContext, tree);
		this.instrTiming = instrTiming;
	}

	@Override
	public int getBCET() {
		return this.instrTiming.getBcet();
	}

	@Override
	public int getWCET() {
		return this.instrTiming.getWcet();
	}

	@Override
	public void setBCET(int bcet) {
		this.instrTiming.setBcet(bcet);
	}

	@Override
	public void setWCET(int wcet) {
		this.instrTiming.setWcet(wcet);	
	}
	
}
