package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.RealVariable;

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
        if(dynRegion.stackSlotTable.lookup(expr.number) != null ){
            int slot = dynRegion.stackSlotTable.lookup(expr.number)[0];
            String type = dynRegion.slotTypeTable.lookup(slot);
            if (type == null) {
                type = dynRegion.walaNumTypesTable.lookup(expr.number);
            }
            if (type == null) throw new IllegalArgumentException("Couldn't figure out type for " + expr);
            return createGreenVar(type, varId);
        }
        else
            return expr;
    }
}
