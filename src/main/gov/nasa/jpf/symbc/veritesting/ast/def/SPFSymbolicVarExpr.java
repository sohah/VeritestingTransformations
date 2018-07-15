package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;

// Note - I don't quite know how SPF Stores symbolic vars so for now
// I am leaving it blank.

public class SPFSymbolicVarExpr extends Expr implements VarExpr {

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
