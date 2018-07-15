package gov.nasa.jpf.symbc.veritesting.ast.visitors;

import gov.nasa.jpf.symbc.veritesting.ast.def.Ast;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.UnaryOpInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;

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
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt a) {
        ind();
        write((gov.nasa.jpf.symbc.veritesting.ast.def.Expr)a.lhs); write(" := "); write(a.rhs); write("; "); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt a) {
        write(a.s1);
        write(a.s2);
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt a) {
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
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.SkipStmt a) {
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
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayStoreInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.BinaryOpInstruction c) {
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
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ConversionInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ComparisonInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.SwitchInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ReturnInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.GetInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.PutInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.NewInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.InvokeInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.ThrowInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.CheckCastInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.InstanceOfInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.PhiInstruction c) {
        ind();
        write(c.original.toString()); nl();
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.GreenExpr expr) {
        ind();
        write(expr.toString());
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.WalaComparisonExpr expr) {
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
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr expr) {
        write("(field_ref_var " + expr.fieldRef.toString() + " " + expr.subscript);
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.SPFSymbolicVarExpr expr) {
        write("(spf_symbolic_var <unknown>!)");
        return null;
    }

    @Override
    public Void visit(gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr expr) {
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
