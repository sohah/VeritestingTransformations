package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class IntConstant implements VeriExpression {
    private int constant;

    public int getConstant() {
        return constant;
    }

    public void setConstant(int constant) {
        this.constant = constant;
    }


    @Override
    public String toString() {
        return String.valueOf(constant);
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitIntConstant(this);
    }
}
