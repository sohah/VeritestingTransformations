package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ExpUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression>{

    int uniqueNum;

    ExpUniqueVisitor(int uniqueNum){
        super();
        this.uniqueNum = uniqueNum;
    }

    @Override
    public Expression visit(WalaVarExpr expr){
        String varId = Integer.toString(expr.number);
        varId = varId.concat(Integer.toString(uniqueNum));
        int newNumber = Integer.valueOf(varId);
        return new WalaVarExpr(newNumber);
    }
}
