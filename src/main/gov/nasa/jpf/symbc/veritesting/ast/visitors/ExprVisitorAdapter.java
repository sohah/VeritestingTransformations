package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

public class ExprVisitorAdapter<T>  {

    private ExprVisitor<T> theVisitor;

    public ExprVisitorAdapter(ExprVisitor<T> theVisitor) {
        this.theVisitor = theVisitor;
    }

    // doing a kind of gross thing since the visitor support I like is not
    // built into Green: forcing the issue with a bunch of type tests.
    public T accept(Expression e) {
        if (e instanceof IntConstant) {
            return theVisitor.visit((IntConstant) e);
        } else if (e instanceof IntVariable) {
            return theVisitor.visit((IntVariable) e);
        } else if (e instanceof Operation) {
            return theVisitor.visit((Operation) e);
        } else if (e instanceof RealConstant) {
            return theVisitor.visit((RealConstant) e);
        } else if (e instanceof RealVariable) {
            return theVisitor.visit((RealVariable) e);
        } else if (e instanceof StringConstantGreen) {
            return theVisitor.visit((StringConstantGreen) e);
        } else if (e instanceof StringVariable) {
            return theVisitor.visit((StringVariable) e);
        } else if (e instanceof FieldRefVarExpr) {
            return theVisitor.visit((FieldRefVarExpr) e);
        } else if (e instanceof GammaVarExpr) {
            return theVisitor.visit((GammaVarExpr) e);
        } else if (e instanceof WalaVarExpr) {
            return theVisitor.visit((WalaVarExpr) e);
        } else if (e instanceof IfThenElseExpr) {
            return theVisitor.visit((IfThenElseExpr) e);
        } else {
            throw new IllegalArgumentException("Unknown class in ExprVisitorAdapter!");
        }
    }

}