package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

// TODO: MWW: THIS IS JUST A PLACEHOLDER!  I DID NOT WANT TO DEAL WITH SWITCH TODAY.

public class SwitchInstruction extends Instruction {


    public SwitchInstruction(SSAInstruction ins) {
        super(ins);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
