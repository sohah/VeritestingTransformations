package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public class Composition implements VeritestingStatement {
    private VeritestingStatement s1;
    private VeritestingStatement s2;

    public Composition(VeritestingStatement s1, VeritestingStatement s2) {
        this.s1 = s1;
        this.s2 = s2;
    }

    @Override
    public String toString() {
        return s1.toString() + ";" + s2.toString();
    }
}

