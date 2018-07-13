package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeritestingExpression;

public class IfThenElse implements VeritestingStatement {
    private VeritestingExpression condition;
    private VeritestingStatement s1;
    private VeritestingStatement s2;

    public IfThenElse(VeritestingExpression condition, VeritestingStatement s1, VeritestingStatement s2) {
        this.condition = condition;
        this.s1 = s1;
        this.s2 = s2;
    }


    public VeritestingExpression getCondition() {
        return condition;
    }

    public void setCondition(VeritestingExpression condition) {
        this.condition = condition;
    }

    public VeritestingStatement getS1() {
        return s1;
    }

    public void setS1(VeritestingStatement s1) {
        this.s1 = s1;
    }

    public VeritestingStatement getS2() {
        return s2;
    }

    public void setS2(VeritestingStatement s2) {
        this.s2 = s2;
    }

    @Override
    public String toString() {
        return " if " + this.condition + " then " + s1.toString() + " else " + s2.toString();
    }
}
