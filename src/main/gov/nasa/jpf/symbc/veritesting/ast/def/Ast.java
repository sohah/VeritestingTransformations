package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public interface Ast {
     public abstract <T, S extends T> T accept(AstVisitor<T, S> visitor);

}
