package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class Gamma implements VeriExpression {
    private VeriExpression condition;
    private Var var1;
    private Var var2;


    public Gamma(VeriExpression condition, Var var1, Var var2) {
        this.condition = condition;
        this.var1 = var1;
        this.var2 = var2;
    }

    public VeriExpression getCondition() {
        return condition;
    }

    public void setCondition(VeriExpression condition) {
        this.condition = condition;
    }

    public Var getVar1() {
        return var1;
    }

    public void setVar1(Var var1) {
        this.var1 = var1;
    }

    public Var getVar2() {
        return var2;
    }

    public void setVar2(Var var2) {
        this.var2 = var2;
    }

    @Override
    public String toString() {
        return " Gamma( " + condition.toString() + ", " + var1.toString() + ", " + var2.toString() +")";

    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitGamma(this);
    }
}
