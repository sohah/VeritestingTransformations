package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;


public class SPFCaseStmt implements Stmt {

    public final Expression spfCondition;
    public final SPFReason reason;

    public enum SPFReason{
        OBJECT_CREATION, OUT_OF_BOUND_EXCEPTION;
    }

    public SPFCaseStmt(Expression spfCondition, SPFReason reason) {
        this.spfCondition = spfCondition;
        this.reason = reason;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "SPFCaseStmt( " + reason + "," + spfCondition.toString() + ")";
    }

}
