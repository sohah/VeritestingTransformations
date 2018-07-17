package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class IfThenElseStmt implements Stmt {
    public final Expression condition;
    public final Stmt thenStmt;
    public final Stmt elseStmt;

    public IfThenElseStmt(Expression condition, Stmt thenStmt, Stmt elseStmt) {
        this.condition = condition;
        this.thenStmt = thenStmt;
        this.elseStmt = elseStmt;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return " if (" + this.condition + ") then (" + thenStmt.toString() + ") else (" + elseStmt.toString() + ")";
    }
}
