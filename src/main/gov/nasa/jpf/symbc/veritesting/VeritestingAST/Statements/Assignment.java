package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeritestingExpression;

public class Assignment implements VeritestingStatement {
    public Assignment(Var lhs, VeritestingExpression rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    private Var lhs;
    private VeritestingExpression rhs;

    public Var getLhs() {
        return lhs;
    }

    public VeritestingExpression getRhs() {
        return rhs;
    }

    @Override
    public String toString() {
        return lhs.toString() + ":=" + rhs.toString();
    }
}
