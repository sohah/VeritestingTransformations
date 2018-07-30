package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;

public class ExpUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression>{

    int uniqueNum;
    DynamicRegion dynRegion;

    ExpUniqueVisitor(DynamicRegion dynRegion, int uniqueNum){
        super();
        this.uniqueNum = uniqueNum;
        this.dynRegion = dynRegion;
    }

    @Override
    public Expression visit(WalaVarExpr expr){
        String varId = "w" + Integer.toString(expr.number);
        varId = varId.concat(Integer.toString(uniqueNum));
        if(dynRegion.slotParamTable.lookup(expr.number) != null ){
            int slot = dynRegion.slotParamTable.lookup(expr.number)[0];
            return createGreenVar(dynRegion.slotTypeTable.lookup(slot), varId);
        }
        else
            return expr;
    }
}
