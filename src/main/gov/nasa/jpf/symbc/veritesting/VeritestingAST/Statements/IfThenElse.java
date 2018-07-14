package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;

public class IfThenElse implements VeriStatment {
    private VeriExpression condition;
    private VeriStatment s1;
    private VeriStatment s2;

    public IfThenElse(VeriExpression condition, VeriStatment s1, VeriStatment s2) {
        this.condition = condition;
        this.s1 = s1;
        this.s2 = s2;
    }


    public VeriExpression getCondition() {
        return condition;
    }

    public void setCondition(VeriExpression condition) {
        this.condition = condition;
    }

    public VeriStatment getS1() {
        return s1;
    }

    public void setS1(VeriStatment s1) {
        this.s1 = s1;
    }

    public VeriStatment getS2() {
        return s2;
    }

    public void setS2(VeriStatment s2) {
        this.s2 = s2;
    }

    @Override
    public String toString() {
        return " if (" + this.condition + ") then (" + s1.toString() + ") else (" + s2.toString() + ")";
    }

    @Override
    public Object visit(VeriStatVisitor v) {
        return v.visitIfThenElse(this);
    }
}
