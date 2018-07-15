package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SPFSymbolicVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;

public interface VVarExprVisitor<T> {
    public T visit(WalaVarExpr expr);
    public T visit(FieldRefVarExpr expr);
    public T visit(SPFSymbolicVarExpr expr);
    public T visit(GammaVarExpr expr);
}
