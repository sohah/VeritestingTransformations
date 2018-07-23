package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;

public class UniqueRegion {
    public static void doUniqueness(DynamicRegion dynRegion){

        DynamicRegion.uniqueCounter++;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(dynRegion);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);
        Stmt dynStmt = dynRegion.getDynStmt().accept(stmtVisitor);
        dynRegion.setDynStmt(dynStmt);
    }
}
