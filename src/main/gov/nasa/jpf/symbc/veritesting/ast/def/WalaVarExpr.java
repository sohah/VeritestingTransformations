package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;

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
