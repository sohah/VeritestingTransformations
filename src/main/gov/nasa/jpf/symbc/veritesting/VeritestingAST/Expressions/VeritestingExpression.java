package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public interface VeritestingExpression {
    public String toString();
    public void visit(VeriExpressionVisitor v);
}
