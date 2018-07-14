package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

public interface VeriStatVisitor {
    void visitSPFCase(SPFCase spfCase);
    void visitSkip(Skip skip);
    void visitIfThenElse(IfThenElse ifThenElse);
    void visitComposition(Composition composition);
    void visitAssignment(Assignment assignment);
}
