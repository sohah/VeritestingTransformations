package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.*;


public class ExprIdVisitor implements ExprVisitor<Expression> {
    @Override public Expression visit(IntConstant expr) {
        return expr;
    }
    @Override public Expression visit(IntVariable expr) {
        return expr;
    }
    @Override public Expression visit(Operation expr) { return expr; }
    @Override public Expression visit(RealConstant expr) {
        return expr;
    }
    @Override public Expression visit(RealVariable expr) {
        return expr;
    }
    @Override public Expression visit(StringConstantGreen expr) {
        return expr;
    }
    @Override public Expression visit(StringVariable expr) {
        return expr;
    }
    @Override public Expression visit(WalaVarExpr expr) {
        return expr;
    }
    @Override public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }
    @Override public Expression visit(GammaVarExpr expr) { return expr; }
    @Override public Expression visit(IfThenElseExpr expr) { return expr; }
}