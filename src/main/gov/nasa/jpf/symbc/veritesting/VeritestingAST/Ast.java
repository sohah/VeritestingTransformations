package gov.nasa.jpf.symbc.veritesting.VeritestingAST;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public interface Ast {
     public abstract <T, S extends T> T accept(AstVisitor<T, S> visitor);

}
