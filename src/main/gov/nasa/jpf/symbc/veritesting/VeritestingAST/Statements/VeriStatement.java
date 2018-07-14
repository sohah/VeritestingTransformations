package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public interface VeriStatement {

    public String toString();
    public void visitor(VeriStatVisitor v);
}
