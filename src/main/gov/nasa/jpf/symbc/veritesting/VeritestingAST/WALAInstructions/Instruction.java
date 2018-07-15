package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Stmt;

public abstract class Instruction implements Stmt {
    public final SSAInstruction original;

    public Instruction(SSAInstruction original) {
        this.original = original;
    }

}
