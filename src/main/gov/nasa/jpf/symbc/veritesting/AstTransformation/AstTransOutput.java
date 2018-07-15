package gov.nasa.jpf.symbc.veritesting.AstTransformation;


//SH: This class is used to hold the output of the transformation process of a single basic block.
// a "statement" is what the basic block has translated into and a "continuation" is part of the
// translated statement that could change if there are more blocks in the graph that needs to
// be nested.

/*
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
*/