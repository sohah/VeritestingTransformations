package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAComparisonInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Stmt;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions.Instruction;

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
