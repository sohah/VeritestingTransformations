package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public class Skip implements VeriStatment {

    @Override
    public String toString() {
        return "skip; ";
    }

    @Override
    public Object visit(VeriStatVisitor v) {
        return v.visitSkip(this);
    }

}
