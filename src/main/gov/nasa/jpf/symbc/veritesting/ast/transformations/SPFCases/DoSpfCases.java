package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.StmtPrintVisitor;

public class DoSpfCases {
    StaticRegion staticRegion;

    public DoSpfCases(StaticRegion staticRegion) {
        this.staticRegion = staticRegion;
        generateSPFCases();
    }

    public void generateSPFCases() {
        SpfCasesVisitor spfCasesVisitor = new SpfCasesVisitor();
        Stmt substitutedStmt = staticRegion.getStaticStmt().accept(spfCasesVisitor);
        staticRegion.setStaticStmt(substitutedStmt);
        System.out.println("--------------- SPFCases TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(staticRegion.getStaticStmt()));
    }
}
