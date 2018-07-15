package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.FieldRef;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.ExprVisitor;

public class FieldRefVarExpr extends Expr implements VarExpr {
    public final gov.nasa.jpf.symbc.veritesting.VeritestingAST.FieldRef fieldRef;
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
