package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import cvc3.Expr;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/**
 * Unique region creator, of both conditional regions and method regions.
 */

public class UniqueRegion {

    /**
     * Used to create a unique conditional region.
     *
     * @param staticRegion Dynamic region that needs to be unique.
     * @return A new static region that is unique.
     */

    public static DynamicRegion execute(StaticRegion staticRegion) throws CloneNotSupportedException, StaticRegionException {

        ++DynamicRegion.uniqueCounter;
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);


        Stmt dynStmt = staticRegion.staticStmt.accept(stmtVisitor);

        DynamicRegion dynRegion = new DynamicRegion(staticRegion,
                dynStmt, uniqueNum);


        System.out.println("\n--------------- UNIQUENESS TRANSFORMATION ---------------");
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        dynRegion.slotParamTable.print();
        dynRegion.inputTable.print();
        dynRegion.varTypeTable.print();
        dynRegion.outputTable.print();

        return dynRegion;
    }

    public static DynamicRegion execute(DynamicRegion oldDynRegion) throws StaticRegionException, CloneNotSupportedException {
        int uniqueNum = DynamicRegion.uniqueCounter;
        ExpUniqueVisitor expUniqueVisitor = new ExpUniqueVisitor(uniqueNum);
        if (expUniqueVisitor.sre != null) throwException(expUniqueVisitor.sre, INSTANTIATION);
        AstMapVisitor stmtVisitor = new AstMapVisitor(expUniqueVisitor);

        Stmt dynStmt = oldDynRegion.dynStmt.accept(stmtVisitor);
        RemoveEarlyReturns.ReturnResult oldEarlyReturn = oldDynRegion.earlyReturnResult;
        DynamicRegion newDynRegion;
        if (oldEarlyReturn.hasER()) { //make early return result (assign and condition) unique as well.
            ExprVisitorAdapter eva = new ExprVisitorAdapter(expUniqueVisitor);
            Expression newAssign = (Expression) eva.accept(oldEarlyReturn.assign);
            Expression newCondition = (Expression) eva.accept(oldEarlyReturn.condition);

            RemoveEarlyReturns o = new RemoveEarlyReturns();
            RemoveEarlyReturns.ReturnResult newReturnResult = o.new ReturnResult(oldEarlyReturn.stmt, newAssign, newCondition, oldEarlyReturn.retPosAndType);
            newReturnResult.retVar = oldEarlyReturn.retVar;
            newDynRegion = new DynamicRegion(oldDynRegion,
                    dynStmt,
                    oldDynRegion.spfCaseList, oldDynRegion.regionSummary, oldDynRegion.spfPredicateSummary, newReturnResult);
        } else {
            newDynRegion = new DynamicRegion(oldDynRegion,
                    dynStmt,
                    oldDynRegion.spfCaseList, oldDynRegion.regionSummary, oldDynRegion.spfPredicateSummary, oldDynRegion.earlyReturnResult);
        }

        newDynRegion.fieldRefTypeTable.makeUniqueKey(uniqueNum);
        newDynRegion.psm.setUniqueNum(uniqueNum);
        newDynRegion.arrayPSM.setUniqueNum(uniqueNum);
        return newDynRegion;
    }

}
