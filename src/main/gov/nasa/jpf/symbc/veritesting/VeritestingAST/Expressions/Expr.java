package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Ast;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.ExprVisitor;

public abstract class Expr implements Ast {

    @Override
    public <T, S extends T> S accept(AstVisitor<T, S> visitor) {
        return accept((ExprVisitor<S>) visitor);
    }

    public abstract <S> S accept(ExprVisitor<S> visitor);

}
