package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.StackFrame;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;

import gov.nasa.jpf.symbc.numeric.*;

public class IXOR extends gov.nasa.jpf.jvm.bytecode.IXOR {

	@Override
	public Instruction execute (SystemState ss, KernelState ks, ThreadInfo th) {
		StackFrame sf = th.getTopFrame();
		IntegerExpression sym_v1 = (IntegerExpression) sf.getOperandAttr(0); 
		IntegerExpression sym_v2 = (IntegerExpression) sf.getOperandAttr(1);
		
		if(sym_v1==null && sym_v2==null)
			return super.execute(ss, ks, th); // we'll still do the concrete execution
		else 
			throw new RuntimeException("## Error: SYMBOLIC IXOR not supported");
	
	}

}
