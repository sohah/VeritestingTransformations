package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.Type;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import jkind.lustre.Equation;
import jkind.lustre.VarDecl;
import za.ac.sun.cs.green.expr.*;

import java.util.ArrayList;

public class DeclarationExprVisitor implements ExprVisitor {
    private final DynamicRegion dynamicRegion;
    private final InOutManager inOutManager;
    public ArrayList<VarDecl> declarationList;

    public DeclarationExprVisitor(DynamicRegion dynamicRegion, InOutManager inOutManager) {
        this.dynamicRegion = dynamicRegion;
        this.inOutManager = inOutManager;
    }

    @Override
    public Object visit(IntConstant expr) {
        return null;
    }

    @Override
    public Object visit(IntVariable expr) {
        if (inOutManager.isInOutVar(expr.toString(), Type.INT)) { // if it is not input or output in it is a local var that we car about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), )
        }
        return null;
    }

    @Override
    public Object visit(Operation expr) {
        return null;
    }

    @Override
    public Object visit(RealConstant expr) {
        return null;
    }

    @Override
    public Object visit(RealVariable expr) {
        if (inOutManager.isInOutVar(expr.toString(), Type.FLOAT)) { // if it is not input or output in it is a local var that we car about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), )
        }
        return null;
    }

    @Override
    public Object visit(StringConstantGreen expr) {
        return null;
    }

    @Override
    public Object visit(StringVariable expr) {
        if (inOutManager.isInOutVar(expr.toString(), Type.STRING)) { // if it is not input or output in it is a local var that we car about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), )
        }
        return null;
    }

    @Override
    public Object visit(IfThenElseExpr expr) {
        return null;
    }

    @Override
    public Object visit(ArrayRefVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(WalaVarExpr expr) {
        Object rangerType = dynamicRegion.varTypeTable.lookupByName(expr.toString());
        assert (rangerType instanceof String);
        if (inOutManager.isInOutVar(expr.toString(), Type.INT)) { // if it is not input or output in it is a local var that we car about adding
            VarDecl lusterVar = new VarDecl(expr.toString(), )
        }
        return null;
    }

    @Override
    public Object visit(FieldRefVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(GammaVarExpr expr) {
        return null;
    }

    @Override
    public Object visit(AstVarExpr expr) {
        return null;
    }
}
