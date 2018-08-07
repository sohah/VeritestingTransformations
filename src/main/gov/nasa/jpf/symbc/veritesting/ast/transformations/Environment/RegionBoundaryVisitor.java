package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

//SH: this visitor explores the boundaries of the region by identifying: first def, last def and first use vars

import com.ibm.wala.ssa.SSAInvokeInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprBoundaryVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class RegionBoundaryVisitor extends AstMapVisitor {
    private int lastDef;
    private boolean firstDefFound = false;
    private int firstDef;


    public RegionBoundaryVisitor(ExprBoundaryVisitor exprBoundaryVisitor) {
        super(exprBoundaryVisitor);
    }

    public int getLastDef() {
        return lastDef;
    }

    public int getFirstDef() {
        return firstDef;
    }

    public int getFirstUse() {
        return ((ExprBoundaryVisitor)exprVisitor).getFirstUse();
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        lastDef = ((WalaVarExpr)a.lhs).number;
        if (!firstDefFound) {
            firstDef = ((WalaVarExpr)a.lhs).number;
            firstDefFound = true;
        }
        eva.accept(a.rhs);
        return null;
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return null;
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        eva.accept(a.condition);
        a.thenStmt.accept(this);
        a.elseStmt.accept(this);
        return null;
    }

    @Override
    public Stmt visit(SkipStmt a) {
        return null;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return null;
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        lastDef = ((WalaVarExpr)c.def).number;
        if (!firstDefFound) {
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }
        return null;
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        eva.accept(c.arrayref);
        eva.accept(c.index);
        eva.accept(c.assignExpr);
        return null;
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        if (c.original.hasDef()) {
            lastDef = c.getOriginal().getDef();
            if (!firstDefFound) {
                firstDef = c.original.getDef();
                firstDefFound = true;
            }
        }
        eva.accept(c.rhs);
        return null;
    }

    @Override
    public Stmt visit(GetInstruction c) {
        lastDef = ((WalaVarExpr)c.def).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }

        eva.accept(c.ref);
        return null;
    }

    @Override
    public Stmt visit(PutInstruction c) {
        eva.accept(c.def);
        eva.accept(c.assignExpr);
        return null;
    }

    @Override
    public Stmt visit(NewInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        if(((SSAInvokeInstruction) c.original).getNumberOfReturnValues() != 0){
        lastDef = c.original.getDef();
            if(!firstDefFound){
                firstDef = c.original.getDef();
                firstDefFound = true;
            }
        }
        for(int i = 0; i < c.params.length; i++){
            eva.accept(c.params[i]);
        }
        return null;
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        lastDef = ((WalaVarExpr)c.def).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }
        eva.accept(c.arrayref);
        return null;
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return null;
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        lastDef = c.original.getDef();
        if(!firstDefFound){
            firstDef = c.original.getDef();
            firstDefFound = true;
        }
        eva.accept(c.val);
        return null;
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        lastDef = ((WalaVarExpr)c.result).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.result).number;
            firstDefFound = true;
        }
        eva.accept(c.val);

        return null;
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        lastDef = ((WalaVarExpr)c.def).number;
        if(!firstDefFound){
            firstDef = ((WalaVarExpr)c.def).number;
            firstDefFound = true;
        }
        for(int i = 0; i < c.rhs.length; i++){
            eva.accept(c.rhs[i]);
        }

        return null;
    }


}
