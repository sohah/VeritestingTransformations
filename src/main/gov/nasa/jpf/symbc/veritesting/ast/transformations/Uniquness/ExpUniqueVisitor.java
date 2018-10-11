package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;

import static gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr.getUniqueWalaVarExpr;

/**
 * Unique Expression Visitor that ensures the uniqueness of vars used inside the region.
 */
public class ExpUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {


    ArrayList<WalaVarExpr> uniqueSafeList;

    int uniqueNum;
    StaticRegionException sre = null;

    private HashMap<Integer, Variable> varToNumUniqueMap = null;

    ExpUniqueVisitor(int uniqueNum, HashMap<Integer, Variable> varToNumUniqueMap) {
        super();
        this.uniqueNum = uniqueNum;
        this.varToNumUniqueMap = varToNumUniqueMap;
    }

    public ExpUniqueVisitor(int uniqueNum) {
        super();
        this.uniqueNum = uniqueNum;
    }

    /**
     * A visit to all WalaVariables to create a new-unique object for the same var number.
     *
     * @param expr WalaVariable that is visited
     * @return either a new unique wala var object or already an existing unique wala var object.
     */
    @Override
    public Expression visit(WalaVarExpr expr) {
        if (varToNumUniqueMap != null) {
            if (varToNumUniqueMap.containsKey(expr.number))
                return varToNumUniqueMap.get(expr.number);
            else {
                WalaVarExpr walaVar = getUniqueWalaVarExpr(expr, uniqueNum);
                varToNumUniqueMap.put(expr.number, walaVar);
                return walaVar;
            }
        } else return expr;
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
