package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.ExprVisitor;

public class WalaVarExpr extends Expr implements VarExpr {

    public final int number;

    public WalaVarExpr(int var) {
        this.number = var;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

}
