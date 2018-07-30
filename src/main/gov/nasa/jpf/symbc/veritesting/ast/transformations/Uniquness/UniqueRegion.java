package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SlotTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation.WalaNumTypesTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;

public class UniqueRegion {

    public static DynamicRegion execute(DynamicRegion dynRegion){

        if((++DynamicRegion.uniqueCounter)% 10 == 0){
            ++DynamicRegion.uniqueCounter; //just to skip numbers with zero on the right handside
        }
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(dynRegion, uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);
        Stmt uniqStmt = dynRegion.dynStmt.accept(stmtVisitor);


        SlotParamTable slotParamTable = dynRegion.slotParamTable.clone();
        SlotTypeTable slotTypeTable = dynRegion.slotTypeTable;
        WalaNumTypesTable walaNumTypesTable = dynRegion.walaNumTypesTable.clone();
        ValueSymbolTable valueSymbolTable = dynRegion.valueSymbolTable.clone();
        OutputTable outputTable = dynRegion.outputTable.clone();

        slotParamTable.makeUniqueKey(uniqueNum);
        valueSymbolTable.makeUniqueKey(uniqueNum);
        outputTable.makeUniqueKey(uniqueNum);
        walaNumTypesTable.makeUniqueKey(uniqueNum);


        return new DynamicRegion(dynRegion.staticRegion, uniqStmt, slotTypeTable, walaNumTypesTable, valueSymbolTable,
                slotParamTable, outputTable, dynRegion.spfCaseSet);
    }
}
