package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ExpFieldArrayUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private int uniqueNum;
    StaticRegionException sre = null;

    ExpFieldArrayUniqueVisitor(int uniqueNum) {
        super();
        this.uniqueNum = uniqueNum;
    }

    /**
     * A visit to all FieldRefVarExpr to create a new-unique object for the same var number.
     *
     * @param expr FieldRefVarExpr that is visited
     * @return either a new unique FieldRefVarExpr or already an existing unique FieldRefVarExpr object.
     */
    @Override
    public Expression visit(FieldRefVarExpr expr) {
        FieldRefVarExpr uniqueExpr = expr;
        try {
            uniqueExpr = uniqueExpr.makeUnique(uniqueNum);
        } catch (StaticRegionException e) {
            sre = e;
        }
        return uniqueExpr;
    }

    /**
     * A visit to all ArrayRefVarExpr to create a new-unique object for the same var number.
     *
     * @param expr ArrayRefVarExpr that is visited
     * @return either a new unique ArrayRefVarExpr or already an existing unique ArrayRefVarExpr object.
     */
    @Override
    public Expression visit(ArrayRefVarExpr expr) {
        ArrayRefVarExpr uniqueExpr = expr;
        try {
            uniqueExpr = uniqueExpr.makeUnique(uniqueNum);
        } catch (StaticRegionException e) {
            sre = e;
        }
        return uniqueExpr;
    }
}
