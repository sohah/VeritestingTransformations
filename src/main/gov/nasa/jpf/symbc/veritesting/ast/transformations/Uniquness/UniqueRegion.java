package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;

public class UniqueRegion {

    public static DynamicRegion execute(DynamicRegion dynRegion){

        if((++DynamicRegion.uniqueCounter)% 10 == 0){
            ++DynamicRegion.uniqueCounter; //just to skip numbers with zero on the right handside
        }
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(dynRegion, uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);
        Stmt dynStmt = dynRegion.dynStmt.accept(stmtVisitor);


        SlotParamTable slotParamTable = dynRegion.slotParamTable.clone();
        SlotTypeTable slotTypeTable = dynRegion.slotTypeTable;
        VarTypeTable varTypeTable = dynRegion.varTypeTable.clone();
        OutputTable outputTable = dynRegion.outputTable.clone();

        slotParamTable.makeUniqueKey(uniqueNum);
        outputTable.makeUniqueKey(uniqueNum);
        varTypeTable.makeUniqueKey(uniqueNum);


        return new DynamicRegion(dynRegion.staticRegion,
                dynStmt,
                slotTypeTable,
                varTypeTable,
                slotParamTable,
                outputTable,
                dynRegion.isMethodRegion,
                dynRegion.spfCaseSet);
    }
}
