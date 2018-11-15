package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import com.ibm.wala.types.TypeName;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayExpressions;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;

import java.util.Iterator;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ClassUtils.getType;
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

    @Override
    public Stmt visit(CheckCastInstruction c) {
        //TODO: Check if this cast can be done correctly. I (Vaibhav) am assuming it must be correct to get the motivating example to work
        if (c.declaredResultTypes.length != 1)
            throwException(new IllegalArgumentException("Cannot handle checkcast with more than 1 declared result type"), INSTANTIATION);
        TypeName typeName = c.declaredResultTypes[0].getName();
        String type = getType(typeName);
        dynRegion.varTypeTable.add(c.result, type);
        dynRegion.varTypeTable.add(c.val, type);
        Expression rhs = c.val;
        Expression lhs = c.result;
        rhs = eva.accept(rhs);
        if (isConstant(rhs) || isVariable(rhs)) {
            constantsTable.add((Variable) lhs, rhs);
        }
        return new AssignmentStmt(lhs, rhs);
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
        if (dynRegion.constantsTable == null)
            dynRegion.constantsTable = visitor.constantsTable;
        else dynRegion.constantsTable.addAll(visitor.constantsTable);
        simplifyArrayOutputs(dynRegion);

        DynamicRegion ret = new DynamicRegion(dynRegion, stmt, dynRegion.spfCaseList, dynRegion.regionSummary,
                dynRegion.spfPredicateSummary);
//        System.out.println("\n--------------- AFTER SIMPLIFICATION ---------------\n");
//        System.out.println(StmtPrintVisitor.print(ret.dynStmt));
        return ret;
    }

    private static void simplifyArrayOutputs(DynamicRegion dynRegion) {
        ArrayExpressions newOutputs = dynRegion.arrayOutputs.clone();
        Iterator refItr = newOutputs.table.entrySet().iterator();
        while(refItr.hasNext()) {
            Map.Entry<Integer, Expression[]> entry = (Map.Entry<Integer, Expression[]>) refItr.next();
            Expression[] values = entry.getValue();
            for (int i = 0; i < values.length; i++) {
                if (values[i] instanceof Variable && dynRegion.constantsTable.lookup((Variable) values[i]) != null) {
                    values[i] = dynRegion.constantsTable.lookup((Variable) values[i]);
                }
            }
        }
        dynRegion.arrayOutputs = newOutputs;
    }
}