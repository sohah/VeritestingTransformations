package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * Unique region creator, of both conditional regions and method regions.
 */

public class UniqueRegion {

    /**
     * Used to create a unique conditional region.
     * @param dynRegion Dynamic region that needs to be unquie.
     * @return A new dynamic region that is unique.
     */
    public static DynamicRegion execute(DynamicRegion dynRegion){

        if((++DynamicRegion.uniqueCounter)% 10 == 0){
            ++DynamicRegion.uniqueCounter; //just to skip numbers with zero on the right handside
        }
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);
        Stmt dynStmt = dynRegion.dynStmt.accept(stmtVisitor);


        SlotParamTable slotParamTable = dynRegion.slotParamTable.clone();
        VarTypeTable varTypeTable = dynRegion.varTypeTable.clone();
        FieldRefTypeTable fieldRefTypeTable = dynRegion.fieldRefTypeTable.clone();
        OutputTable outputTable = dynRegion.outputTable.clone();

        slotParamTable.makeUniqueKey(uniqueNum);
        outputTable.makeUniqueKey(uniqueNum);
        varTypeTable.makeUniqueKey(uniqueNum);
        fieldRefTypeTable.makeUniqueKey(uniqueNum);


        return new DynamicRegion(dynRegion.staticRegion,
                dynStmt,
                varTypeTable,
                fieldRefTypeTable,
                slotParamTable,
                outputTable,
                dynRegion.isMethodRegion,
                dynRegion.spfCaseSet);
    }

    /**
     * Used to ensure uniquness of high Order region.
     * @param hgOrdStmtRetTypePair this is a triple of Stmt, method return Expression and VarTypeTable of the region method.
     * @return this is the same triple passed to the method, only now unique by appending the a unique prefix.
     */
    public Pair<Stmt, VarTypeTable> executeMethodRegion(Pair<Stmt, VarTypeTable> hgOrdStmtRetTypePair){

        if((++DynamicRegion.uniqueCounter)% 10 == 0){
            ++DynamicRegion.uniqueCounter; //just to skip numbers with zero on the right handside
        }
        int uniqueNum = DynamicRegion.uniqueCounter;

        Stmt dynStmt = hgOrdStmtRetTypePair.getFirst();
        VarTypeTable varTypeTable = hgOrdStmtRetTypePair.getSecond();

        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);
        Stmt uniqueDynStmt = dynStmt.accept(stmtVisitor);

        VarTypeTable uniqueVarTypeTable = varTypeTable.clone();
        uniqueVarTypeTable.makeUniqueKey(uniqueNum);


        return new Pair(uniqueDynStmt, uniqueVarTypeTable);
    }

}
