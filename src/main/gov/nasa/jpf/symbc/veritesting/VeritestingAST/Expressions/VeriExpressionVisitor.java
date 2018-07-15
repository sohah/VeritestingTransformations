package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions.*;

public interface VeriExpressionVisitor {
    void visitFieldReferenceVar(FieldRefVar var);
    void visitWalaVar(WalaVar var);
    void visitGamma(Gamma gamma);
    void visitGreen(GreenExpression expression);
    void visitIntConstant(IntConstant intConstant);
    void visitWalaInstruction(WalaInstruction instruction);

    void visitArrayLengthVeriSSA(SSAArrayLengthInstruction ssaArrayLengthInstruction);

    void visitArrayLoadSSA(SSAArrayLoadInstruction ssaArrayLoadInstruction);

    void visitBinaryOpSSA(SSABinaryOpInstruction ssaBinaryOpInstruction);

    void visitCheckCastSSA(SSACheckCastInstruction ssaCheckCastInstruction);

    void visitComparisonSSA(SSAComparisonInstruction ssaComparisonInstruction);

    void visitConditionalBranchSSA(SSAConditionalBranchInstruction ssaConditionalBranchInstruction);

    void visitConversionSSA(SSAConversionInstruction ssaConversionInstruction);

    void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction);

    void visitGetInstruction(SSAGetInstruction ssaGetInstruction);

    void visitGoToSSA(SSAGotoInstruction ssaGotoInstruction);

    void visitInstanceOfSSA(SSAInstanceofInstruction ssaInstanceofInstruction);

    void visitInvokeSSA(SSAInvokeInstruction ssaInvokeInstruction);

    void visitUnaryOpSSA(SSAUnaryOpInstruction ssaUnaryOpInstruction);

    void visitThrowSSA(SSAThrowInstruction ssaThrowInstruction);

    void visitPhiSSA(SSAPhiInstruction ssaPhiInstruction);

    void visitPutInstruction(SSAPutInstruction ssaPutInstruction);

    void visitReturnInstruction(SSAReturnInstruction ssaReturnInstruction);

    void visitNewInstruction(SSANewInstruction ssaNewInstruction);

    void visitSwitchInstruction(SSASwitchInstruction ssaSwitchInstruction);
}
