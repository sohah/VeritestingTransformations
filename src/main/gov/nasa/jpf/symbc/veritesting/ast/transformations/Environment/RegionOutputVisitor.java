package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

//SH: this visitor visits all statments to obtain the last def var.

import com.ibm.wala.ssa.SSAInvokeInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprRegionInputVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import za.ac.sun.cs.green.expr.Expression;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit.DEF;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit.USE;

public class RegionOutputVisitor implements AstVisitor {
    private int lastVar;
    private boolean firstDefFound = false;

    private int firstDef;

    public int getLastVar() {
        return lastVar;
    }

    @Override
    public Object visit(AssignmentStmt a) {
        lastVar = ((WalaVarExpr)a.lhs).number;
        if (!firstDefFound) {
            firstDef = ((WalaVarExpr)a.lhs).number;
            firstDefFound = true;
        }
        return null;
    }

    @Override
    public Object visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return null;
    }

    @Override
    public Object visit(IfThenElseStmt a) {
        a.thenStmt.accept(this);
        a.elseStmt.accept(this);
        return null;
    }

    @Override
    public Object visit(SkipStmt a) {
        return null;
    }

    @Override
    public Object visit(SPFCaseStmt c) {
        return null;
    }

    @Override
    public Object visit(ArrayLoadInstruction c) {
        lastVar = ((WalaVarExpr)c.def).number;
        if (!firstDefFound) {
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }
        return null;
    }

    @Override
    public Object visit(ArrayStoreInstruction c) {
        return null;
    }

    @Override
    public Object visit(SwitchInstruction c) {
        return null;
    }

    @Override
    public Object visit(ReturnInstruction c) {
        if (c.original.hasDef()) {
            lastVar = c.getOriginal().getDef();
            if (!firstDefFound) {
                firstDef = c.original.getDef();
                firstDefFound = true;
            }
        }
        return null;
    }

    @Override
    public Object visit(GetInstruction c) {
        lastVar = ((WalaVarExpr)c.def).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }
        return null;
    }

    @Override
    public Object visit(PutInstruction c) {
        return null;
    }

    @Override
    public Object visit(NewInstruction c) {
        return null;
    }

    @Override
    public Object visit(InvokeInstruction c) {
        if(((SSAInvokeInstruction) c.original).getNumberOfReturnValues() != 0){
        lastVar = c.original.getDef();
            if(!firstDefFound){
                firstDef = c.original.getDef();
                firstDefFound = true;
            }
        }
        return null;
    }

    @Override
    public Object visit(ArrayLengthInstruction c) {
        lastVar = ((WalaVarExpr)c.def).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }        return null;
    }

    @Override
    public Object visit(ThrowInstruction c) {
        return null;
    }

    @Override
    public Object visit(CheckCastInstruction c) {
        lastVar = c.original.getDef();
        if(!firstDefFound){
            firstDef = c.original.getDef();
            firstDefFound = true;
        }
        return null;
    }

    @Override
    public Object visit(InstanceOfInstruction c) {
        lastVar = ((WalaVarExpr)c.result).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.result).number;
            firstDefFound = true;
        }
        return null;
    }

    @Override
    public Object visit(PhiInstruction c) {
        lastVar = ((WalaVarExpr)c.def).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }
        return null;
    }

    public int getFirstDef() {
        return firstDef;
    }
}
