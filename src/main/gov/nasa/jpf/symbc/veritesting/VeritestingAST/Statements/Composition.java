package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public class Composition implements VeriStatement {
    private VeriStatement s1;
    private VeriStatement s2;

    public Composition(VeriStatement s1, VeriStatement s2) {
        this.s1 = s1;
        this.s2 = s2;
    }

    @Override
    public String toString() {
        return s1.toString() + ";" + s2.toString();
    }

    @Override
    public void visitor(VeriStatVisitor v) {
        v.visitComposition(this);
    }
}

