package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.*;

/*
    The central difficulty here is determining the condition under which to
    assign a variable underneath an IfThenElseExpr and/or Gamma expr.

    NOTE: When Green adds support for IfThenElse expressions, this will become
    unnecessary...maybe we should just add it there.

    This is also an example where supporting an argument in a visitor would be
    quite nice.  Oh well.
 */

public class AstToGreenExprVisitor implements ExprVisitor<Expression> {

    Expression toAssign;
    Expression currentCondition;
    ExprVisitorAdapter<Expression> eva;

    public AstToGreenExprVisitor() {
        this.toAssign = toAssign;
        this.currentCondition = Operation.TRUE;
        eva = new ExprVisitorAdapter<Expression>(this);
    }


    public void setAssign(Expression toAssign) {
        this.toAssign = toAssign;
    }

    public static Expression bad(Object obj) {
        String name = obj.getClass().getCanonicalName();
        throw new IllegalArgumentException("Unsupported class: " + name + " value: " + obj.toString() + " seen in AstToGreenExprVisitor");
    }

    public Expression assign(Expression e) {
        Expression assign = new Operation(Operation.Operator.EQ, toAssign, e);
        if (currentCondition.equals(Operation.TRUE)) {
            return assign;

        } else {
            return new Operation(Operation.Operator.IMPLIES, currentCondition, assign);
        }
    }

    public Expression ite(Expression cond, Expression thenExpr, Expression elseExpr) {
        Expression prevCond = currentCondition;
        Expression thenCond = new Operation(Operation.Operator.AND, currentCondition, cond);
        Expression elseCond = new Operation(Operation.Operator.AND, currentCondition,
                new Operation(Operation.Operator.NOT, cond));
        currentCondition = thenCond;
        Expression thenBranches = eva.accept(thenExpr);
        currentCondition = elseCond;
        Expression elseBranches = eva.accept(elseExpr);
        Expression finalExpr = new Operation(Operation.Operator.OR, thenBranches, elseBranches);
        return finalExpr;
    }

    @Override public Expression visit(GammaVarExpr expr) {
        return ite(expr.condition, (Expression)expr.thenExpr, (Expression)expr.elseExpr);
    }
    @Override public Expression visit(IfThenElseExpr expr) {
        return ite(expr.condition, expr.thenExpr, expr.elseExpr);
    }

    @Override public Expression visit(WalaVarExpr expr) { return bad(expr);  }
    @Override public Expression visit(FieldRefVarExpr expr) { return bad(expr); }
    @Override public Expression visit(IntConstant expr) { return assign(expr); }
    @Override public Expression visit(IntVariable expr) { return assign(expr); }
    @Override public Expression visit(Operation expr) { return assign(expr); }
    @Override public Expression visit(RealConstant expr) { return assign(expr); }
    @Override public Expression visit(RealVariable expr) { return assign(expr); }
    @Override public Expression visit(StringConstantGreen expr) { return assign(expr); }
    @Override public Expression visit(StringVariable expr) { return assign(expr); }
}
