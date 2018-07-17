package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

// TODO: placeholder class: I don't think we need to adequately translate this.

public class NewInstruction extends Instruction {

    public NewInstruction(SSAInstruction ins) {
        super(ins);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
