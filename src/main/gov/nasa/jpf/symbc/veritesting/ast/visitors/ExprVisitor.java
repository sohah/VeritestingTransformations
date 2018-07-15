package gov.nasa.jpf.symbc.veritesting.ast.visitors;


import gov.nasa.jpf.symbc.veritesting.ast.def.GreenExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaComparisonExpr;

public interface ExprVisitor<T> extends VVarExprVisitor<T> {
    public T visit(GreenExpr expr);
    public T visit(WalaComparisonExpr expr);
}
