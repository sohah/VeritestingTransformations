package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public class Skip implements VeriStatement {

    @Override
    public String toString() {
        return "skip; ";
    }

    @Override
    public void visitor(VeriStatVisitor v) {
        v.visitSkip(this);
    }
}
