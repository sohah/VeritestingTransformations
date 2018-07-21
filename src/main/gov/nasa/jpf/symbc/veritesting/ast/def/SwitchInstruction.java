package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSASwitchInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

// TODO: MWW: THIS IS JUST A PLACEHOLDER!  I DID NOT WANT TO DEAL WITH SWITCH TODAY.

public class SwitchInstruction extends Instruction {


    public SwitchInstruction(SSASwitchInstruction ins) {
        super(ins);
    }

    public SSASwitchInstruction getOriginal() {
        return (SSASwitchInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
