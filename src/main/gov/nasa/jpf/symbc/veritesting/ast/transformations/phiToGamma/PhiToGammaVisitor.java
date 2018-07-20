package gov.nasa.jpf.symbc.veritesting.ast.transformations.phiToGamma;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import za.ac.sun.cs.green.expr.Expression;


// God save the queen and those who invented visitors
public class PhiToGammaVisitor extends AstMapVisitor {

    private Stmt lastIfThenElse = null;

    public PhiToGammaVisitor() {
        super(new ExprMapVisitor());
    }

    @Override
    public Stmt visit(CompositionStmt a) {
        if (a.s1 instanceof IfThenElseStmt && a.s2 instanceof PhiInstruction)
            lastIfThenElse = a.s1;
        return super.visit(a);
    }

    @Override
    public Stmt visit(PhiInstruction c) {
        Expression cond = ((IfThenElseStmt)lastIfThenElse).condition;
        IfThenElseStmt ites = (IfThenElseStmt) lastIfThenElse;
        //TODO: add support for nested regions
        // Regions containing other regions with a single phi instruction at the converging node will have more than 2
        // uses on the RHS. IfThenElseStmt for such regions will have one of takenIndex, notTakenIndex be -1
        if (ites.takenIndex != -1 && ites.notTakenIndex != -1) {
            Expression takenExpr = c.rhs[((IfThenElseStmt) lastIfThenElse).takenIndex];
            Expression notTakenExpr = c.rhs[((IfThenElseStmt) lastIfThenElse).notTakenIndex];
            Expression rhs = new GammaVarExpr(cond, takenExpr, notTakenExpr);
            return new AssignmentStmt(c.def, rhs);
        } else return super.visit(c);
    }
}
