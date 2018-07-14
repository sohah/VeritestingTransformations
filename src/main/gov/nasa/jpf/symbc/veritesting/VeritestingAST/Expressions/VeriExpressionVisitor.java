package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public interface VeriExpressionVisitor {
    public void visitFieldReferenceVar(FieldReferenceVar var);
    public void visitWalaVar(WalaVar var);
    public void visitGamma(Gamma gamma);
    public void visitGreen(GreenExpression expression);
    public void visitIntConstant(IntConstant intConstant);
    public void visitWalaInstruction(WalaInstruction instruction);
}
