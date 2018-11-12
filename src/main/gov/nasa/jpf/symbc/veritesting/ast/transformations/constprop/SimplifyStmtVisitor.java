package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.*;
import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class SimplifyStmtVisitor extends AstMapVisitor {
    public ExprVisitorAdapter<Expression> eva;
    private DynamicTable<Expression> constantsTable;
    public StaticRegionException sre = null;
    private DynamicRegion dynRegion;

    private SimplifyStmtVisitor(DynamicRegion dynRegion, DynamicTable<Expression> constantsTable) {
        super(new SimplifyRangerExprVisitor(constantsTable));
        eva = super.eva;
        this.constantsTable = constantsTable;
        this.dynRegion = dynRegion;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        Expression rhs = eva.accept(a.rhs);
        if (isConstant(rhs) || isVariable(rhs)) {
            constantsTable.add((Variable) a.lhs, rhs);
            if (isVariable(rhs)) {
                String type = getGreenVariableType(rhs);
                if (type == null) type = (String) dynRegion.varTypeTable.lookup(rhs);
                if (type == null) type = dynRegion.fieldRefTypeTable.lookup(rhs);
                if (type != null) {
                    if (a.lhs instanceof WalaVarExpr)
                        dynRegion.varTypeTable.add(a.lhs, type);
                    else if (a.lhs instanceof FieldRefVarExpr || a.lhs instanceof ArrayRefVarExpr)
                        dynRegion.fieldRefTypeTable.add((CloneableVariable) a.lhs, type);
                }
            }
            return SkipStmt.skip;
        }
        return new AssignmentStmt(a.lhs, rhs);
    }

    @Override
    public Stmt visit(IfThenElseStmt c) {
        Expression cond = eva.accept(c.condition);
        ExprUtil.SatResult satResult;
        satResult = isSatGreenExpression(cond);
        if (satResult == ExprUtil.SatResult.FALSE) {
            StatisticManager.ifRemovedCount++;
            return c.elseStmt.accept(this);
        } else if (satResult == ExprUtil.SatResult.TRUE) {
            StatisticManager.ifRemovedCount++;
            return c.thenStmt.accept(this);
        } else {
            return new IfThenElseStmt(c.original, cond, c.thenStmt.accept(this), c.elseStmt.accept(this));
        }
    }

    public static DynamicRegion execute(DynamicRegion dynRegion) throws StaticRegionException {
        DynamicTable<Expression> constantsTable = new DynamicTable<>("Constants Table", "Expression", "Constant Value");
        SimplifyStmtVisitor visitor = new SimplifyStmtVisitor(dynRegion, constantsTable);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        if (visitor.sre != null)
            throwException(visitor.sre, INSTANTIATION);
        if (((SimplifyRangerExprVisitor)visitor.exprVisitor).sre != null) {
            throwException(((SimplifyRangerExprVisitor)visitor.exprVisitor).sre, INSTANTIATION);
        }
        dynRegion.constantsTable = visitor.constantsTable;
        DynamicRegion ret = new DynamicRegion(dynRegion, stmt, dynRegion.spfCaseList, dynRegion.regionSummary,
                dynRegion.spfPredicateSummary, dynRegion.earlyReturnResult);
        System.out.println("\n--------------- AFTER SIMPLIFICATION ---------------\n");
        System.out.println(StmtPrintVisitor.print(ret.dynStmt));
        return ret;
    }
}