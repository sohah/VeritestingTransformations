package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ExpUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression>{

    private DynamicRegion dynRegion;
    ExpUniqueVisitor(DynamicRegion dynRegion){
        super();
        this.dynRegion = dynRegion;
    }

    @Override
    public Expression visit(WalaVarExpr expr){
        String varId = Integer.toString(expr.number);
        varId = varId.concat(Integer.toString(DynamicRegion.uniqueCounter));
        int newNumber = Integer.valueOf(varId);
        updateEvn(expr.number, newNumber );
        return new WalaVarExpr(newNumber);
    }

    private void updateEvn(int oldNumber, int newNumber) {
        dynRegion.getStackSlotTable().updateKeys(oldNumber, newNumber);
        dynRegion.getValueSymbolTable().updateKeys(oldNumber, newNumber);
        dynRegion.getVarTypeTable().updateKeys(oldNumber, newNumber);
        dynRegion.getOutputTable().updateKeys(oldNumber, newNumber);

    }
}
