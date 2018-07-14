package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public interface VeriExpression {
    public String toString();
    public void visit(VeriExpressionVisitor v);
}
