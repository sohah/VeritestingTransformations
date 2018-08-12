package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;

/**
 * An interface for Wala vars, fieldRef vars and GammaExpr Vars in RangerIR.
 * @param <T>
 */
public interface VVarExprVisitor<T> {
    public T visit(WalaVarExpr expr);
    public T visit(FieldRefVarExpr expr);
    public T visit(GammaVarExpr expr);
}
