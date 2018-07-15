package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

// TODO: placeholder class: I don't think we need to adequately translate this.

public class ThrowInstruction extends Instruction {

    public ThrowInstruction(SSAThrowInstruction ins) {
        super(ins);
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
