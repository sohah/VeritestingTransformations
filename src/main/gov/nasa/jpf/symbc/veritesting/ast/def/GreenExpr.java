package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class GreenExpr extends Expr {
    public final Expression greenExpr;

    public GreenExpr(Expression e) {
        greenExpr = e;
    }

    @Override
    public String toString() {
        return super.toString();
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

}
