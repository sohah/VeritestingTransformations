package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;

public abstract class Instruction implements Stmt {
    public final SSAInstruction original;

    public Instruction(SSAInstruction original) {
        this.original = original;
    }

}
