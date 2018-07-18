package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class CompositionStmt implements Stmt {
    public final Stmt s1;
    public final Stmt s2;

    public CompositionStmt(Stmt s1, Stmt s2) {
        this.s1 = s1;
        this.s2 = s2;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "(( "+ s1.toString() + ") ; (" + s2.toString() + "))";
    }


}

