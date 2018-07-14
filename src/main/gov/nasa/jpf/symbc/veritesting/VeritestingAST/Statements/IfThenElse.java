package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;

public class IfThenElse implements VeriStatement {
    private VeriExpression condition;
    private VeriStatement s1;
    private VeriStatement s2;

    public IfThenElse(VeriExpression condition, VeriStatement s1, VeriStatement s2) {
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

    public VeriStatement getS1() {
        return s1;
    }

    public void setS1(VeriStatement s1) {
        this.s1 = s1;
    }

    public VeriStatement getS2() {
        return s2;
    }

    public void setS2(VeriStatement s2) {
        this.s2 = s2;
    }

    @Override
    public String toString() {
        return " if " + this.condition + " then " + s1.toString() + " else " + s2.toString();
    }

    @Override
    public void visitor(VeriStatVisitor v) {
        v.visitIfThenElse(this);
    }
}
