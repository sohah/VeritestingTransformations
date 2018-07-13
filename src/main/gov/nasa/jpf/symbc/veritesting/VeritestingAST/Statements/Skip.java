package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeritestingExpression;

public class Skip implements VeritestingStatement {

    @Override
    public String toString() {
        return "skip; ";
    }
}
