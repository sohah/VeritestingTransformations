package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.VeritestingStatement;

public class AstTransOutput {
    private VeritestingStatement statement;
    private VeritestingStatement continuation;

    public AstTransOutput(VeritestingStatement statement, VeritestingStatement continuation) {
        this.statement = statement;
        this.continuation = continuation;
    }

    public VeritestingStatement getStatement() {
        return statement;
    }

    public void setStatement(VeritestingStatement statement) {
        this.statement = statement;
    }

    public VeritestingStatement getContinuation() {
        return continuation;
    }

    public void setContinuation(VeritestingStatement continuation) {
        this.continuation = continuation;
    }
}
