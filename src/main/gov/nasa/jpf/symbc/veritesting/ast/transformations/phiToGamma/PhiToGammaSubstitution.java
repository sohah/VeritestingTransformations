package gov.nasa.jpf.symbc.veritesting.ast.transformations.phiToGamma;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Region;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;

/*
Vaibhav: The purpose of this class is to visit all the statements in a statement list and replace any phis with gammas
 */
public class PhiToGammaSubstitution {
    private Region region;
    public PhiToGammaSubstitution(Region region) {
        this.region = region;
    }

    public void doSubstitution() {
        PhiToGammaVisitor visitor = new PhiToGammaVisitor();
        Stmt s = region.getStmt().accept(visitor);
        region.setStmt(s);
        System.out.println("Printing regions after PhiToGammaSubstitution:");
        System.out.println(StmtPrintVisitor.print(region.getStmt()));
    }
}
