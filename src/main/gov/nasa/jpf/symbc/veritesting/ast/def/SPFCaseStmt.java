package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is SPFCases in RangerIR. These are basically a place holder for places in RangerIR where SPF needs to explore.
 */

public class SPFCaseStmt implements Stmt {

    public final Expression spfCondition;
    public final SPFReason reason;

    /**
     * These are the different reasons that requires SPF exploration.
     */
    public enum SPFReason{
        OBJECT_CREATION, THROW,
        MULTIPLE, OUT_OF_BOUND_EXCEPTION; //used when the two sides of the ifStmt have SPFCases
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
