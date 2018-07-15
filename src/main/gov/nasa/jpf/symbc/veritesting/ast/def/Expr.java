package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;

public abstract class Expr implements Ast {

    @Override
    public <T, S extends T> S accept(AstVisitor<T, S> visitor) {
        return accept((ExprVisitor<S>) visitor);
    }

    public abstract <S> S accept(ExprVisitor<S> visitor);

}
