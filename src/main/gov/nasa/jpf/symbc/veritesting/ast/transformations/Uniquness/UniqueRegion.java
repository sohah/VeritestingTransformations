package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;

/**
 * Unique region creator, of both conditional regions and method regions.
 */

public class UniqueRegion {

    /**
     * Used to create a unique conditional region.
     * @param staticRegion Dynamic region that needs to be unique.
     * @return A new static region that is unique.
     */
    public static StaticRegion execute(StaticRegion staticRegion){

        if((++DynamicRegion.uniqueCounter)% 10 == 0){
            ++DynamicRegion.uniqueCounter; //just to skip numbers with zero on the right handside
        }
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);
        Stmt staticStmt = staticRegion.staticStmt.accept(stmtVisitor);


        SlotParamTable slotParamTable = staticRegion.slotParamTable.clone();
        VarTypeTable varTypeTable = staticRegion.varTypeTable.clone();
        OutputTable outputTable = staticRegion.outputTable.clone();
        InputTable inputTable = staticRegion.inputTable.clone();

        slotParamTable.makeUniqueKey(uniqueNum);
        outputTable.makeUniqueVal(uniqueNum);
        varTypeTable.makeUniqueKey(uniqueNum);
        inputTable.makeUniqueKey(uniqueNum);



        StaticRegion uniqueStaticRegion = new StaticRegion(staticRegion.ir,
                staticStmt,
                slotParamTable,
                outputTable,
                inputTable,
                varTypeTable,
                staticRegion.endIns,
                staticRegion.isMethodRegion);
/*
        System.out.println("\n--------------- UNIQUENESS TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(uniqueStaticRegion.staticStmt));
        uniqueStaticRegion.slotParamTable.print();
        uniqueStaticRegion.inputTable.print();
        uniqueStaticRegion.varTypeTable.print();
        uniqueStaticRegion.outputTable.print();*/

        return uniqueStaticRegion;
    }

}
