/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.symbc.realtime.JOPUtil;
import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;
import gov.nasa.jpf.vm.Instruction;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class JOPNode extends RTNode implements IHasWCET {

	private int wcet;
	
	public JOPNode(InstrContext instructionContext) {
		super(instructionContext);
		Instruction instr = instructionContext.getInstr();
		this.wcet = JOPUtil.getWCET(instr);
		
		/*Add the method switch cost if the instruction is a return instruction
		* Note that we assume 'worst-case behavior' in terms of the cache - a
		* cache miss is assumed to always occur
		*/
		if(instr instanceof ReturnInstruction)
			this.wcet += JOPUtil.calculateMethodSwitchCost(false, ((ReturnInstruction)instr).getMethodInfo());
	}

	public JOPNode(InstrContext instructionContext, SymbolicExecutionTree tree) {
		super(instructionContext, tree);
		this.wcet = JOPUtil.getWCET(instructionContext.getInstr());
	}

	@Override
	public int getWCET() {
		return this.wcet;
	}

	@Override
	public void setWCET(int wcet) {
		this.wcet = wcet;		
	}
}
