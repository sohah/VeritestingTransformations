package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticEnvironment.OutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticEnvironment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DynamicEnvironment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DynamicEnvironment.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DynamicEnvironment.SlotTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticEnvironment.VarTypeTable;
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
        VarTypeTable varTypeTable = dynRegion.varTypeTable.clone();
        ValueSymbolTable valueSymbolTable = dynRegion.valueSymbolTable.clone();
        OutputTable outputTable = dynRegion.outputTable.clone();

        slotParamTable.makeUniqueKey(uniqueNum);
        valueSymbolTable.makeUniqueKey(uniqueNum);
        outputTable.makeUniqueKey(uniqueNum);
        varTypeTable.makeUniqueKey(uniqueNum);


        return new DynamicRegion(dynRegion.staticRegion, uniqStmt, slotTypeTable, varTypeTable, valueSymbolTable,
                slotParamTable, outputTable, dynRegion.spfCaseSet);
    }
}
