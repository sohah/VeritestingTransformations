package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.*;

public class ExprMapVisitor implements ExprVisitor<Expression> {

    ExprVisitorAdapter<Expression> eva =
            new ExprVisitorAdapter<>(this);

    @Override
    public Expression visit(IntConstant expr) {
        return expr;
    }

    @Override
    public Expression visit(IntVariable expr) {
        return expr;
    }

    @Override
    public Expression visit(Operation expr) {
        Expression [] operands = new Expression [expr.getArity()];
        int index = 0;
        for (Expression e: expr.getOperands()) {
            operands[index++] = eva.accept(e);
        }
        return new Operation(expr.getOperator(), operands);
    }

    @Override
    public Expression visit(RealConstant expr) {
        return expr;
    }

    @Override
    public Expression visit(RealVariable expr) {
        return expr;
    }

    @Override
    public Expression visit(StringConstantGreen expr) {
        return expr;
    }

    @Override
    public Expression visit(StringVariable expr) {
        return expr;
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        return expr;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        return new GammaVarExpr(eva.accept(expr.condition),
                (VarExpr)eva.accept((Expression)expr.thenExpr),
                (VarExpr)eva.accept((Expression)expr.elseExpr));
    }
}
