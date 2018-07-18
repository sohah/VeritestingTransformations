package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class IfThenElseStmt implements Stmt {
    public final Expr condition;
    public final Stmt thenStmt;
    public final Stmt elseStmt;
    public final SSAConditionalBranchInstruction original;

    public IfThenElseStmt(SSAConditionalBranchInstruction original, Expr condition, Stmt thenStmt, Stmt elseStmt) {
        this.original = original;
        this.condition = condition;
        this.thenStmt = thenStmt;
        this.elseStmt = elseStmt;
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return " if (" + this.condition + ") then (" + thenStmt.toString() + ") else (" + elseStmt.toString() + ")";
    }
}
