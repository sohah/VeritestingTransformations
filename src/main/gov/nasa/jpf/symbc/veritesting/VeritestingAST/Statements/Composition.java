package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public class Composition implements VeriStatment {
    private VeriStatment s1;
    private VeriStatment s2;

    public Composition(VeriStatment s1, VeriStatment s2) {
        this.s1 = s1;
        this.s2 = s2;
    }

    public VeriStatment getS1() {
        return s1;
    }

    public void setS1(VeriStatment s1) {
        this.s1 = s1;
    }

    public VeriStatment getS2() {
        return s2;
    }

    public void setS2(VeriStatment s2) {
        this.s2 = s2;
    }

    @Override
    public String toString() {
        return "(( "+ s1.toString() + ") ; (" + s2.toString() + "))";
    }

    @Override
    public Object visit(VeriStatVisitor v) {
        return v.visitComposition(this);
    }

}

