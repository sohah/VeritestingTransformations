package gov.nasa.jpf.symbc.veritesting.ast.transformations.Invariants;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

/* Implements an invariant that checks if the region has up to one stack output */
public class LocalOutputInvariantVisitor extends AstMapVisitor {
    ExprVisitorAdapter<Expression> eva;
    public List<AssignmentStmt> gammaStmts;

    private LocalOutputInvariantVisitor(StaticRegion staticRegion) {
        super(new ExprMapVisitor());
        eva = super.eva;
        gammaStmts = new ArrayList<AssignmentStmt>();
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        if (a.rhs instanceof GammaVarExpr) gammaStmts.add(a);
        return a;
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        a.s1.accept(this);
        a.s2.accept(this);
        return a;
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        a.thenStmt.accept(this);
        a.elseStmt.accept(this);
        gammaStmts.clear();
        return a;
    }

    @Override
    public Stmt visit(SkipStmt a) { return a; }

    @Override
    public Stmt visit(SPFCaseStmt c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ArrayLoadInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ArrayStoreInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(SwitchInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ReturnInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(GetInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(PutInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(NewInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(InvokeInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ArrayLengthInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(ThrowInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(CheckCastInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(InstanceOfInstruction c) { gammaStmts.clear(); return c; }

    @Override
    public Stmt visit(PhiInstruction c) { gammaStmts.clear(); return c; }

    public static boolean execute(StaticRegion staticRegion) throws StaticRegionException {
        LocalOutputInvariantVisitor visitor = new LocalOutputInvariantVisitor(staticRegion);
        staticRegion.staticStmt.accept(visitor);
        for (AssignmentStmt assignmentStmt: visitor.gammaStmts) {
            if (assignmentStmt.rhs instanceof GammaVarExpr && WalaVarExpr.class.isInstance(assignmentStmt.lhs)) {
                WalaVarExpr lhs = (WalaVarExpr) assignmentStmt.lhs;
                boolean outputFound = false;
                Set<Integer> outputSlots = staticRegion.outputTable.table.keySet();
                for (int slot : outputSlots) {
                    if (((Integer) staticRegion.outputTable.lookup(slot)) == lhs.number) outputFound = true;
                }
                if (!outputFound) {
                    if (staticRegion.stackOutput == null) staticRegion.stackOutput = lhs;
                    else
                        throwException(new StaticRegionException("static region with gamma expression has more than one non-local output in lhs"), STATIC);
                }
            }
        }
        return true;
    }
}
