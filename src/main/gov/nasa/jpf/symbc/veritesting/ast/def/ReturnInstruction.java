package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAReturnInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class ReturnInstruction extends Instruction {

    public final Expr rhs;

    public ReturnInstruction(SSAReturnInstruction ins, Expr rhs) {
        super(ins);
        this.rhs = rhs;
    }

    public ReturnInstruction(SSAReturnInstruction ins) {
        super(ins);
        rhs = new WalaVarExpr(ins.getUse(0));
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
