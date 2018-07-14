package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import za.ac.sun.cs.green.expr.Expression;

public class GreenExpression implements VeritestingExpression{
    private Expression expression;

    public Expression getExpression() {
        return expression;
    }

    public void setExpression(Expression expression) {
        this.expression = expression;
    }

    @Override
    public String toString() {
        return super.toString();
    }

    @Override
    public void visit(VeriExpressionVisitor v) {

    }
}
