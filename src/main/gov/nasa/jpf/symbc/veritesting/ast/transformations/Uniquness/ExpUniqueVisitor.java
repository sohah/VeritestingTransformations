package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * Unique Expression Visitor that ensures the uniquness vars used inside the region.
 */
public class ExpUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    ArrayList<WalaVarExpr> uniqueSafeList;

    int uniqueNum;
    private HashMap<Integer, Variable> varToNumUniqueMap;

    ExpUniqueVisitor(int uniqueNum, HashMap<Integer, Variable> varToNumUniqueMap) {
        super();
        this.uniqueNum = uniqueNum;
        this.varToNumUniqueMap = varToNumUniqueMap;
    }

    /**
     * A visit to all WalaVariables to create a new-unique object for the same var number.
     *
     * @param expr WalaVariable that is visited
     * @return either a new unique wala var object or already an existing unique wala var object.
     */
    @Override
    public Expression visit(WalaVarExpr expr) {
        if (varToNumUniqueMap.containsKey(expr.number))
            return varToNumUniqueMap.get(expr.number);
        else {
            String varId = Integer.toString(expr.number);
            varId = varId.concat("$");
            varId = varId.concat(Integer.toString(uniqueNum));
            WalaVarExpr walaVar = new WalaVarExpr(expr.number, varId);
            varToNumUniqueMap.put(expr.number, walaVar);
            return walaVar;
        }
    }
}
