package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.VeriStatement;

public class AstTransOutput {
    private VeriStatement statement;
    private VeriStatement continuation;

    public AstTransOutput(VeriStatement statement, VeriStatement continuation) {
        this.statement = statement;
        this.continuation = continuation;
    }

    public VeriStatement getStatement() {
        return statement;
    }

    public void setStatement(VeriStatement statement) {
        this.statement = statement;
    }

    public VeriStatement getContinuation() {
        return continuation;
    }

    public void setContinuation(VeriStatement continuation) {
        this.continuation = continuation;
    }
}
