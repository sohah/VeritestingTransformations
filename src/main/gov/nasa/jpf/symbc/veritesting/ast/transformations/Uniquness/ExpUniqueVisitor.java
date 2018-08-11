package gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;

public class ExpUniqueVisitor extends ExprMapVisitor implements ExprVisitor<Expression>{

    int uniqueNum;
    VarTypeTable varTypeTable;

    ExpUniqueVisitor(VarTypeTable varTypeTable, int uniqueNum){
        super();
        this.varTypeTable = varTypeTable;
        this.uniqueNum = uniqueNum;
    }

    @Override
    public Expression visit(WalaVarExpr expr){
        String varId = "w" + Integer.toString(expr.number);
        varId = varId.concat(Integer.toString(uniqueNum));

        String type = varTypeTable.lookup(expr.number);

        if (type == null) return expr;
        else return createGreenVar(type, varId);
    }
}
