package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors;


import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.GreenExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaComparisonExpr;

public interface ExprVisitor<T> extends VVarExprVisitor<T> {
    public T visit(GreenExpr expr);
    public T visit(WalaComparisonExpr expr);
}
