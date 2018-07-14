package gov.nasa.jpf.symbc.veritesting.AstTransformation;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVar;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Assignment;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.IfThenElse;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Skip;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.VeritestingStatement;

public class ToStatementIVisitor implements SSAInstruction.IVisitor {
    public VeritestingStatement veritestingStatement;
    public boolean canVeritest = true;

    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) {
        veritestingStatement = new Skip();
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ssaArrayLoadInstruction) {
        WalaVar walaVar = new WalaVar(ssaArrayLoadInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaArrayLoadInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction) {
        WalaVar walaVar = null;
        WalaInstruction walaInstruction = new WalaInstruction(ssaArrayStoreInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ssaBinaryOpInstruction) {
        WalaVar walaVar = new WalaVar(ssaBinaryOpInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaBinaryOpInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ssaUnaryOpInstruction) {
        WalaVar walaVar = new WalaVar(ssaUnaryOpInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaUnaryOpInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitConversion(SSAConversionInstruction ssaConversionInstruction) {
        WalaVar walaVar = new WalaVar(ssaConversionInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaConversionInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitComparison(SSAComparisonInstruction ssaComparisonInstruction) {
        WalaVar walaVar = new WalaVar(ssaComparisonInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaComparisonInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ssaConditionalBranchInstruction) {
        WalaInstruction walaInstruction = new WalaInstruction(ssaConditionalBranchInstruction);
        veritestingStatement = new IfThenElse(walaInstruction, null, null);
    }

    @Override
    public void visitSwitch(SSASwitchInstruction ssaSwitchInstruction) {
        WalaVar walaVar = null;
        WalaInstruction walaInstruction = new WalaInstruction(ssaSwitchInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitReturn(SSAReturnInstruction ssaReturnInstruction) {
        WalaVar walaVar = new WalaVar(ssaReturnInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaReturnInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitGet(SSAGetInstruction ssaGetInstruction) {
        WalaVar walaVar = new WalaVar(ssaGetInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaGetInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitPut(SSAPutInstruction ssaPutInstruction) {
        WalaVar walaVar = null;
        WalaInstruction walaInstruction = new WalaInstruction(ssaPutInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction ssaInvokeInstruction) {
        WalaVar walaVar = new WalaVar(ssaInvokeInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaInvokeInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {
        WalaVar walaVar = new WalaVar(ssaNewInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaNewInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ssaArrayLengthInstruction) {
        WalaVar walaVar = new WalaVar(ssaArrayLengthInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaArrayLengthInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
        WalaVar walaVar = null;
        WalaInstruction walaInstruction = new WalaInstruction(ssaThrowInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction ssaCheckCastInstruction) {
        WalaVar walaVar = new WalaVar(ssaCheckCastInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaCheckCastInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction ssaInstanceofInstruction) {
        WalaVar walaVar = new WalaVar(ssaInstanceofInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaInstanceofInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitPhi(SSAPhiInstruction ssaPhiInstruction) {
        WalaVar walaVar = new WalaVar(ssaPhiInstruction.getDef());
        WalaInstruction walaInstruction = new WalaInstruction(ssaPhiInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
        WalaVar walaVar = null;
        WalaInstruction walaInstruction = new WalaInstruction(ssaGetCaughtExceptionInstruction);
        veritestingStatement = new Assignment(walaVar, walaInstruction);
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {
        canVeritest = false;
    }
}
