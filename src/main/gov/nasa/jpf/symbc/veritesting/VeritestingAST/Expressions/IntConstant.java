package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeritestingExpression;

public class IntConstant implements VeritestingExpression {
    private int constant;

    public int getConstant() {
        return constant;
    }

    public void setConstant(int constant) {
        this.constant = constant;
    }


    @Override
    public String toString() {
        return String.valueOf(constant);
    }
}
