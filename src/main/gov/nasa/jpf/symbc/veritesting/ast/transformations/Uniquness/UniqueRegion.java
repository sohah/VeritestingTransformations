package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * Unique region creator, of both conditional regions and method regions.
 */

public class UniqueRegion {

    /**
     * Used to create a unique conditional region.
     * @param staticRegion Dynamic region that needs to be unique.
     * @return A new static region that is unique.
     */

    public static DynamicRegion execute(StaticRegion staticRegion){

        if((++DynamicRegion.uniqueCounter)% 10 == 0){
            ++DynamicRegion.uniqueCounter; //just to skip numbers with zero on the right handside
        }
        int uniqueNum = DynamicRegion.uniqueCounter;
        HashMap<Integer, Variable> varToNumUniqueMap = new HashMap<>();
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum, varToNumUniqueMap);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);


        Stmt dynStmt = staticRegion.staticStmt.accept(stmtVisitor);

        DynamicRegion dynRegion = new DynamicRegion(staticRegion,
                dynStmt,
                varToNumUniqueMap);

        System.out.println("\n--------------- UNIQUENESS TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        dynRegion.slotParamTable.print();
        dynRegion.inputTable.print();
        dynRegion.varTypeTable.print();
        dynRegion.outputTable.print();

        return dynRegion;
    }

}
