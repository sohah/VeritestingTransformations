package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.AstVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.*;

public class ExprConstPropVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private DynamicTable<Expression> constantsTable;

    public ExprConstPropVisitor(DynamicTable<Expression> constantsTable) {
        super();
        eva = super.eva;
        this.constantsTable = constantsTable;
    }

    private Expression lookup(Expression expr) {
        if (constantsTable.lookup((Variable) expr) != null)
            return constantsTable.lookup((Variable) expr);
        else return expr;
    }


    @Override
    public Expression visit(WalaVarExpr expr) {
        return lookup(expr);
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return lookup(expr);
    }

    @Override
    public Expression visit(IntVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(RealVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(StringVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(AstVarExpr expr) { return lookup(expr); }

    @Override
    public Expression visit(ArrayRefVarExpr expr) { return lookup(expr); }

    @Override
    public Expression visit(Operation expr) {
        //TODO: constant-fold these in when possible by first extracting a method out of ExprUtil.isSatExpression and use the extracted method
        return super.visit(expr);
    }
}
