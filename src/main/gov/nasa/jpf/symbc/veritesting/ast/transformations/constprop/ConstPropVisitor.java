package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isConstant;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isSatExpression;

public class ConstPropVisitor extends AstMapVisitor {
    private ExprVisitorAdapter<Expression> eva;
    private DynamicTable<Expression> constantsTable;

    private ConstPropVisitor(DynamicTable<Expression> constantsTable) {
        super(new ExprConstPropVisitor(constantsTable));
        eva = super.eva;
        this.constantsTable = constantsTable;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        if (isConstant(a.rhs)) {
            constantsTable.add((Variable) a.lhs, a.rhs);
        }
        return new AssignmentStmt(eva.accept(a.lhs), eva.accept(a.rhs));
    }

    @Override
    public Stmt visit(IfThenElseStmt c) {
        Expression cond = eva.accept(c.condition);
        ExprUtil.SatResult satResult = isSatExpression(cond);
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

    public static DynamicRegion execute(DynamicRegion dynRegion) {
        DynamicTable<Expression> constantsTable = new DynamicTable<Expression>("Constants Table", "Expression", "Constant Value");
        ConstPropVisitor visitor = new ConstPropVisitor(constantsTable);
        Stmt stmt = dynRegion.dynStmt.accept(visitor);
        return new DynamicRegion(dynRegion, stmt, dynRegion.spfCaseList, dynRegion.regionSummary, dynRegion.spfPredicateSummary);
    }
}