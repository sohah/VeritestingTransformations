package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;

public interface VarExpr {

    public abstract <T> T accept(ExprVisitor<T> visitor);

}
