package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

//SH: this visitor visits all statements to find the first use of every stack slot.

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.ExprRegionInputVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import za.ac.sun.cs.green.expr.Expression;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit.DEF;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit.USE;

public class RegionInputVisitor extends AstMapVisitor{

    public RegionInputVisitor(InputTable inputTable, SlotParamTable slotParamTable) {
        super(new ExprRegionInputVisitor(inputTable, slotParamTable));
    }
    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, eva.accept(a.rhs));
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        return new CompositionStmt(a.s1.accept(this), a.s2.accept(this));

    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        return new IfThenElseStmt(a.original, eva.accept(a.condition), a.thenStmt.accept(this),
                a.elseStmt.accept(this));
    }

    @Override
    public Stmt visit(SkipStmt a) {
        return a;
    }

    @Override
    public Stmt visit(SPFCaseStmt c) {
        return new SPFCaseStmt(eva.accept(c.spfCondition), c.reason);
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        return new ArrayLoadInstruction(c.getOriginal(),
                eva.accept(c.arrayref),
                eva.accept(c.index),
                c.elementType,
                c.def);
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        return new ArrayStoreInstruction(c.getOriginal(),
                eva.accept(c.arrayref),
                eva.accept(c.index),
                c.elementType,
                eva.accept(c.assignExpr));
    }

    @Override
    public Stmt visit(SwitchInstruction c) {
        return c;
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        return new ReturnInstruction(c.getOriginal(), eva.accept(c.rhs));
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return new GetInstruction(c.getOriginal(),
                c.def,
                eva.accept(c.ref),
                c.field);
    }

    @Override
    public Stmt visit(PutInstruction c) {
        PutInstruction ins = new PutInstruction(c.getOriginal(),
                eva.accept(c.def),
                c.field,
                eva.accept(c.assignExpr));
        return ins;
    }

    @Override
    public Stmt visit(NewInstruction c) {
        return c;
    }

    @Override
    public Stmt visit(InvokeInstruction c) {
        Expression [] params = new Expression [c.params.length];
        for (int i=0; i < params.length; i++) {
            params[i] = eva.accept(c.params[i]);
        }
        return new InvokeInstruction(c.getOriginal(), c.result, params);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return new ArrayLengthInstruction(c.getOriginal(),
                c.def,
                eva.accept(c.arrayref));
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        return new ThrowInstruction(c.getOriginal());
    }

    @Override
    public Stmt visit(CheckCastInstruction c) {
        return new CheckCastInstruction(c.getOriginal(),
                c.result,
                eva.accept(c.val),
                c.declaredResultTypes);
    }

    @Override
    public Stmt visit(InstanceOfInstruction c) {
        return new InstanceOfInstruction(c.getOriginal(),
                c.result,
                eva.accept(c.val),
                c.checkedType);
    }

    @Override
    public Stmt visit(PhiInstruction c) {

        Expression [] rhs = new Expression[c.rhs.length];
        for (int i=0; i < rhs.length; i++) {
            rhs[i] = eva.accept(c.rhs[i]);
        }

        return new PhiInstruction(c.getOriginal(),
                eva.accept(c.def),
                rhs);
    }
}
