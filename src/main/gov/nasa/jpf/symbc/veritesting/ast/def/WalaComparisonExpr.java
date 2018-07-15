package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;

public class WalaComparisonExpr extends Expr {

    public final Expr lhs;
    public final IConditionalBranchInstruction.IOperator op;
    public final Expr rhs;

    public WalaComparisonExpr(Expr lhs, IConditionalBranchInstruction.IOperator op, Expr rhs) {
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }

    public WalaComparisonExpr(SSAConditionalBranchInstruction ins) {
        lhs = new WalaVarExpr(ins.getUse(0));
        op = ins.getOperator();
        rhs = new WalaVarExpr(ins.getUse(1));
    }

    @Override
    public <S> S accept(ExprVisitor<S> visitor) {
        return visitor.visit(this);
    }
}
