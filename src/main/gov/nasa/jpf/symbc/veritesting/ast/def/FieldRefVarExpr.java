package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;

public class FieldRefVarExpr extends Expr implements VarExpr {
    public final FieldRef fieldRef;
    public final int subscript;

    public FieldRefVarExpr(FieldRef fieldRef, int subscript) {
        this.fieldRef = fieldRef;
        this.subscript = subscript;
    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

}
