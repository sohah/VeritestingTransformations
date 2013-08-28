/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class InstrContext {
	
	private final Instruction instr;
	private final StackFrame frame;
	private final PathCondition pc;
	
	public InstrContext(Instruction instr, StackFrame frame) {
		this(instr, frame, null);
	}
	
	public InstrContext(Instruction instr, StackFrame frame, PathCondition pc) {
		this.instr = instr;
		this.frame = frame;
		this.pc = pc;
	}
	
	public Instruction getInstr() {
		return instr;
	}
	
	public StackFrame getFrame() {
		return frame;
	}
	
	public PathCondition getPathCondition() {
		return this.pc;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
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
		InstrContext other = (InstrContext) obj;

		if (frame == null) {
			if (other.frame != null)
				return false;
		} else if (!frame.equals(other.frame)) {
			return false;
		}
		if (instr == null) {
			if (other.instr != null)
				return false;
		} else if(!instr.getMnemonic().equals(other.instr.getMnemonic())) {
			return false;
		} else if(!instr.getFilePos().equals(other.instr.getFilePos())) {
			return false;
		}
		return true;
	}
}
