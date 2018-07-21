package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.Region;
import gov.nasa.jpf.vm.ThreadInfo;

public class DoSubstitution {

    private ThreadInfo ti;
    Region region;

    public DoSubstitution(ThreadInfo ti, Region region) {
        this.ti = ti;
        this.region = region;
        doSubstitution();
    }

    public void doSubstitution() {
        UseOnlyVisitor mapVisitor = new UseOnlyVisitor(ti, region);
        Stmt substitutedStmt = region.getStmt().accept(mapVisitor);
        region.setStmt(substitutedStmt);
        System.out.println("--------------- SUBSTITUTION TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(region.getStmt()));
    }
}
