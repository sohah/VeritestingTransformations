package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Ast;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public interface Stmt extends Ast {
    public abstract <T, S extends T> T accept(AstVisitor<T, S> visitor);
    public String toString();
}
