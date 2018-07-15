package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Ast;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions.*;

public class PrettyPrintVisitor implements AstVisitor<Void, Void> {

    int indent = 0;
    private StringBuilder sb = new StringBuilder();
    private String main;

    void ind() {
        for (int i=0; i < indent; i++) {
            sb.append("   ");
        }
    }

    void indent() {
        indent++;
    }

    void unindent() {
        if (indent > 0)
            indent--;
    }

    void nl() {
        sb.append(System.lineSeparator());
    }

    void write(Ast a) {
        a.accept(this);
    }

    void write(String s) {
        sb.append(s);
    }

    @Override
    public Void visit(AssignmentStmt a) {
        ind();
        write((Expr)a.lhs); write(" := "); write(a.rhs); write("; "); nl();
        return null;
    }

    @Override
    public Void visit(CompositionStmt a) {
        write(a.s1);
        write(a.s2);
        return null;
    }

    @Override
    public Void visit(IfThenElseStmt a) {
        ind();
        write("if ("); write(a.condition); write(") {"); nl();
        indent();
        write(a.thenStmt);
        unindent();
        ind(); write("} else {"); nl();
        indent();
        write(a.elseStmt);
        unindent();
        ind(); write("}"); nl();
        return null;
    }

    @Override
    public Void visit(SkipStmt a) {
        ind();
        write("skip; "); nl();
        return null;
    }

    @Override
    public Void visit(SPFCaseStmt c) {
        ind();
        write("<SPFCase: cond: "); write(c.spfCondition); write(", reason: "); write(c.reason.toString() + ">"); nl();
        return null;
    }

    // TO DO: print these properly :)
    @Override
    public Void visit(ArrayLoadInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(ArrayStoreInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(BinaryOpInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(UnaryOpInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(ConversionInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(ComparisonInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(SwitchInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(ReturnInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(GetInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(PutInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(NewInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(InvokeInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(ArrayLengthInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(ThrowInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(CheckCastInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(InstanceOfInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(PhiInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(GreenExpr expr) {
        ind();
        write(expr.toString());
        return null;
    }

    @Override
    public Void visit(WalaComparisonExpr expr) {
        write(expr.lhs);
        write(" " + expr.op.toString() + " ");
        write(expr.rhs);
        return null;
    }

    @Override
    public Void visit(WalaVarExpr expr) {
        write("(wala_var " + expr.number + ")");
        return null;
    }

    @Override
    public Void visit(FieldRefVarExpr expr) {
        write("(field_ref_var " + expr.fieldRef.toString() + " " + expr.subscript);
        return null;
    }

    @Override
    public Void visit(SPFSymbolicVarExpr expr) {
        write("(spf_symbolic_var <unknown>!)");
        return null;
    }

    @Override
    public Void visit(GammaVarExpr expr) {
        write(expr.toString());
        return null;
    }

    public String toString() {
        return sb.toString();
    }

    public static String print(Ast s) {
        PrettyPrintVisitor visitor = new PrettyPrintVisitor();
        s.accept(visitor);
        return visitor.toString();
    }

}
