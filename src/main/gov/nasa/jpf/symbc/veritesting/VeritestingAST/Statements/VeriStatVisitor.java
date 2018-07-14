package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import choco.cp.solver.constraints.global.geost.geometricPrim.Obj;

public interface VeriStatVisitor {
    Object visitSPFCase(SPFCase spfCase);
    Object visitSkip(Skip skip);
    Object visitIfThenElse(IfThenElse ifThenElse);
    Object visitComposition(Composition composition);
    Object visitAssignment(Assignment assignment);
}
