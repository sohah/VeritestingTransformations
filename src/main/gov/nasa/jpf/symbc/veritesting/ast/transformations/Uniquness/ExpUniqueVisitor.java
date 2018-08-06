package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
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

        String type = null;
        if(dynRegion.slotParamTable.lookup(expr.number) != null ) {
            int slot = dynRegion.slotParamTable.lookup(expr.number)[0];
            type = dynRegion.varTypeTable.lookup(slot);
        }
        if (type == null) {
            type = dynRegion.varTypeTable.lookup(expr.number);
        }
        if (type == null) return expr;
        else return createGreenVar(type, varId);
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        String varId = "@r"+expr.fieldRef.ref + "." + expr.fieldRef.field +
                ".p" + Integer.toString(expr.subscript.pathSubscript) +
                ".g" + Integer.toString(expr.subscript.globalSubscript);
        varId = varId.concat(Integer.toString(uniqueNum));
        String type = dynRegion.varTypeTable.lookup(expr.getName());
        if (type == null) return expr;
        else return createGreenVar(type, varId);
    }
}
