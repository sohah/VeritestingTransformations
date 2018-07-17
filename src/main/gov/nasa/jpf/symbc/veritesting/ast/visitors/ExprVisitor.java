package gov.nasa.jpf.symbc.veritesting.ast.visitors;


import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import za.ac.sun.cs.green.expr.*;

public interface ExprVisitor<T> extends VVarExprVisitor<T> {
    public T visit(IntConstant expr);
    public T visit(IntVariable expr);
    public T visit(Operation expr);
    public T visit(RealConstant expr);
    public T visit(RealVariable expr);
    public T visit(StringConstantGreen expr);
    public T visit(StringVariable expr);
}
