package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;


public class SubstitutionVisitor extends AstMapVisitor{
    ExprVisitorAdapter<Expression> eva;
    private DynamicRegion dynRegion;


    private SubstitutionVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super(new ExprSubstitutionVisitor(ti, dynRegion));
        eva = super.eva;
    }


    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, eva.accept(a.rhs));
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
    public Stmt visit(GetInstruction c) {
        return new GetInstruction(c.getOriginal(),
                c.def,
                eva.accept(c.ref),
                c.field);
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
    public Stmt visit(PhiInstruction c) {

        Expression [] rhs = new Expression[c.rhs.length];
        for (int i=0; i < rhs.length; i++) {
            rhs[i] = eva.accept(c.rhs[i]);
        }

        return new PhiInstruction(c.getOriginal(),
                c.def,
                rhs);
    }

    public static DynamicRegion doSubstitution(ThreadInfo ti, StaticRegion staticRegion)  {
        DynamicRegion dynRegion = new DynamicRegion(staticRegion);
        SubstitutionVisitor visitor = new SubstitutionVisitor(ti, dynRegion);
        Stmt dynStmt = dynRegion.getStaticStmt().accept(visitor);
        dynRegion.setDynStmt(dynStmt);
        return dynRegion;
    }
}
