package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.*;


public class EquationExprVisitor implements ExprVisitor {

    @Override
    public Object visit(IntConstant expr) {
        return null;
    }

    @Override
    public Object visit(IntVariable expr) {
        return null;
    }

    @Override
    public Object visit(Operation expr) {
        return null;
    }

    @Override
    public Object visit(RealConstant expr) {
        return null;
    }

    @Override
    public Object visit(RealVariable expr) {
        return null;
    }

    @Override
    public Object visit(StringConstantGreen expr) {
        return null;
    }

    @Override
    public Object visit(StringVariable expr) {
        return null;
    }

    @Override
    public Object visit(IfThenElseExpr expr) {
        return null;
    }

    @Override
    public Object visit(ArrayRefVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(WalaVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(FieldRefVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(GammaVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(AstVarExpr expr) {
        return null;
    }
}
