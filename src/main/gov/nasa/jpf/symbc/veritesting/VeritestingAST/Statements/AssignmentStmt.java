package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.ExprVisitor;

public class AssignmentStmt implements Stmt {

    public final VarExpr lhs;
    public final Expr rhs;

    public AssignmentStmt(VarExpr lhs, Expr rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    @Override
    public String toString() {
        return lhs.toString() + " := (" + rhs.toString() +" )";
    }

    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
