package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public interface VeriStatment {
    public String toString();
    public Object visit(VeriStatVisitor v);
}
