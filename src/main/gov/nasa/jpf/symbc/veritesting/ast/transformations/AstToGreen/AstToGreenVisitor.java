package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.DefUseVisit;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;


/*
    Preconditions:
        - Only statements are assignment statements and gamma statements

        - All IfThenElse expressions are in "normal form"
            - No IfThenElse/Gamma expressions embedded within expressions other than
              IfThenElse expressions
                e.g.: (if x then y else z) + (if a then b else c)
            - No IfThenElse expressions as conditions of other IfThenElse expressions:
                e.g.: (if (if x then y else z) then a else b)


     */

/**
 * Main visitor that visits all statements and translate them to the appropriate green expression. At the point the expected statements are, assignments, composition and skip.
 */

public class AstToGreenVisitor implements AstVisitor<Expression> {

    ExprVisitorAdapter<Expression> eva;
    AstToGreenExprVisitor exprVisitor;


    public AstToGreenVisitor() {
        exprVisitor = new AstToGreenExprVisitor();
        eva = new ExprVisitorAdapter<>(exprVisitor);
    }

    public Expression bad(Object obj) {
        String name = obj.getClass().getCanonicalName();
        throw new IllegalArgumentException("Unsupported class: " + name +
                " value: " + obj.toString() + " seen in AstToGreenVisitor");
    }


    public Expression assignStmt(AssignmentStmt stmt) {
        exprVisitor.setAssign(stmt.lhs);
        return eva.accept(stmt.rhs);
    }

    /**
     * Transform a composition statement into a conjunction in green.
     * @param stmt The composition statement to be translated.
     * @return A green expression that represents the compsition statement.
     */
    public Expression compositionStmt(CompositionStmt stmt) {
        Expression lhs = transform(stmt.s1);
        Expression rhs = transform(stmt.s2);
        return new Operation(Operation.Operator.AND, lhs, rhs);
    }

    public Expression transform(Stmt stmt) {
        if (stmt instanceof AssignmentStmt) {
            return assignStmt((AssignmentStmt) stmt);
        } else if (stmt instanceof CompositionStmt) {
            return compositionStmt((CompositionStmt) stmt);
        } else if (stmt instanceof SkipStmt) {
            return Operation.TRUE;
        } else {
            return bad(stmt);
        }
    }

    @Override
    public Expression visit(SkipStmt a) {
        return Operation.TRUE;
    }

    @Override
    public Expression visit(AssignmentStmt a) {
        return assignStmt(a);
    }

    @Override
    public Expression visit(CompositionStmt a) {
        return compositionStmt(a);
    }

    @Override
    public Expression visit(IfThenElseStmt a) {
        return bad(a);
    }

    @Override
    public Expression visit(SPFCaseStmt c) {
        return bad(c);
    }

    @Override
    public Expression visit(ArrayLoadInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ArrayStoreInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(SwitchInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ReturnInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(GetInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(PutInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(NewInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(InvokeInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ArrayLengthInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(ThrowInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(CheckCastInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(InstanceOfInstruction c) {
        return bad(c);
    }

    @Override
    public Expression visit(PhiInstruction c) {
        return bad(c);
    }

    public static Expression execut(DynamicRegion dynamicRegion){
        WalaVarToSPFVarVisitor walaVarVisitor = new WalaVarToSPFVarVisitor(dynamicRegion.varTypeTable);
        AstMapVisitor astMapVisitor = new AstMapVisitor(walaVarVisitor);
        Stmt noWalaVarStmt = dynamicRegion.dynStmt.accept(astMapVisitor);
        FieldRefVarToSPFVarVisitor fieldRefVisitor = new FieldRefVarToSPFVarVisitor(dynamicRegion.fieldRefTypeTable);
        astMapVisitor = new AstMapVisitor(fieldRefVisitor);
        Stmt noRangerVarStmt = noWalaVarStmt.accept(astMapVisitor);

        AstToGreenVisitor toGreenVisitor = new AstToGreenVisitor();
        return noRangerVarStmt.accept(toGreenVisitor);

    }
}
