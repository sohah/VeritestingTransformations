package gov.nasa.jpf.symbc.veritesting.AstTransformation;

public class AstTransOutput {
    private Object statement;
    private Object continuation;

    public AstTransOutput(Object statement, Object continuation) {
        this.statement = statement;
        this.continuation = continuation;
    }

    public Object getStatement() {
        return statement;
    }

    public void setStatement(Object statement) {
        this.statement = statement;
    }

    public Object getContinuation() {
        return continuation;
    }

    public void setContinuation(Object continuation) {
        this.continuation = continuation;
    }
}
