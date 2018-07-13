package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import za.ac.sun.cs.green.expr.Expression;

enum SPFReason{
    OBJECT_CREATION, OUT_OF_BOUND_EXCEPTION;
}

public class SPFCase implements VeritestingStatement {

    private Expression spfCondition;
    private SPFReason reason;

    public SPFCase(Expression spfCondition, SPFReason reason) {
        this.spfCondition = spfCondition;
        this.reason = reason;
    }

    public Expression getSpfCondition() {
        return spfCondition;
    }

    public void setSpfCondition(Expression spfCondition) {
        this.spfCondition = spfCondition;
    }

    @Override
    public String toString() {
        return "SPFCase( " + reason + "," + spfCondition.toString() + ")";
    }

    public SPFReason getReason() {
        return reason;
    }

    public void setReason(SPFReason reason) {
        this.reason = reason;
    }
}
