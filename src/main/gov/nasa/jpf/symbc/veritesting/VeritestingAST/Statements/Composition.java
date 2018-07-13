package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public class Composition implements VeritestingStatement {
    VeritestingStatement s1;
    VeritestingStatement s2;

    @Override
    public String toString() {
        return s1.toString() + ";" + s2.toString();
    }
}

