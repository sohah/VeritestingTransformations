package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFSymbolicVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;

public interface VVarExprVisitor<T> {
    public T visit(WalaVarExpr expr);
    public T visit(FieldRefVarExpr expr);
    public T visit(SPFSymbolicVarExpr expr);
    public T visit(GammaVarExpr expr);
}
