package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;


public class SPFCaseStmt implements Stmt {

    public final Expr spfCondition;
    public final SPFReason reason;

    public enum SPFReason{
        OBJECT_CREATION, OUT_OF_BOUND_EXCEPTION;
    }

    public SPFCaseStmt(Expr spfCondition, SPFReason reason) {
        this.spfCondition = spfCondition;
        this.reason = reason;
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "SPFCaseStmt( " + reason + "," + spfCondition.toString() + ")";
    }

}
