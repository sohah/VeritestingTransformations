package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSANewInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

// TODO: placeholder class: I don't think we need to adequately translate this.

public class NewInstruction extends Instruction {

    public NewInstruction(SSANewInstruction ins) {
        super(ins);
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
