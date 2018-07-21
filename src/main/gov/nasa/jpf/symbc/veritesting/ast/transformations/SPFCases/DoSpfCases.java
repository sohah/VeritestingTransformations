package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.Region;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.StmtPrintVisitor;

public class DoSpfCases {
    Region region;

    public DoSpfCases(Region region) {
        this.region = region;
        generateSPFCases();
    }

    public void generateSPFCases() {
        SpfCasesVisitor spfCasesVisitor = new SpfCasesVisitor();
        Stmt substitutedStmt = region.getStmt().accept(spfCasesVisitor);
        region.setStmt(substitutedStmt);
        System.out.println("--------------- SUBSTITUTION TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(region.getStmt()));
    }
}
