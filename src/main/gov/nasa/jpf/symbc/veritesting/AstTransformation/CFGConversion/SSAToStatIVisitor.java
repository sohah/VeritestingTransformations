package gov.nasa.jpf.symbc.veritesting.AstTransformation.CFGConversion;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.SkipStmt;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements.Stmt;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions.*;


//SH: This class translates SSAInstructions to Veritesting Statements.
// many of the assignment instructions have the left hand side as an "EmptyVar" because none
// has been constructed at this point yet.


public class SSAToStatIVisitor implements SSAInstruction.IVisitor {
    public Stmt veriStatement;
    public boolean canVeritest = true;

    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) {
        throw new IllegalArgumentException("Goto seen in SSAToStatIVisitor.  This is a mistake!");
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ssaArrayLoadInstruction) {
        veriStatement = new ArrayLoadInstruction(ssaArrayLoadInstruction);
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction) {
        veriStatement = new ArrayStoreInstruction(ssaArrayStoreInstruction);
    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ssaBinaryOpInstruction) {
        veriStatement = new BinaryOpInstruction(ssaBinaryOpInstruction);
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ssaUnaryOpInstruction) {
        veriStatement = new UnaryOpInstruction(ssaUnaryOpInstruction);
    }

    @Override
    public void visitConversion(SSAConversionInstruction ssaConversionInstruction) {
        veriStatement = new ConversionInstruction(ssaConversionInstruction);
    }

    @Override
    public void visitComparison(SSAComparisonInstruction ssaComparisonInstruction) {
        veriStatement = new ComparisonInstruction(ssaComparisonInstruction);
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ssaConditionalBranchInstruction) {
        throw new IllegalArgumentException("Reached conditional branch in SSAToStatIVisitor: why?");
    }

    @Override
    public void visitSwitch(SSASwitchInstruction ssaSwitchInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitReturn(SSAReturnInstruction ssaReturnInstruction) {
        veriStatement = new ReturnInstruction(ssaReturnInstruction);
    }

    @Override
    public void visitGet(SSAGetInstruction ssaGetInstruction) {
        veriStatement = new GetInstruction(ssaGetInstruction);
    }

    @Override
    public void visitPut(SSAPutInstruction ssaPutInstruction) {
        veriStatement = new PutInstruction(ssaPutInstruction);
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction ssaInvokeInstruction) {
        veriStatement = new InvokeInstruction(ssaInvokeInstruction);
    }

    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {
        veriStatement = new NewInstruction(ssaNewInstruction);
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ssaArrayLengthInstruction) {
        veriStatement = new ArrayLengthInstruction(ssaArrayLengthInstruction);
    }

    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
        veriStatement = new ThrowInstruction(ssaThrowInstruction);
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction ssaCheckCastInstruction) {
        veriStatement = new CheckCastInstruction(ssaCheckCastInstruction);
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction ssaInstanceofInstruction) {
        veriStatement = new InstanceOfInstruction(ssaInstanceofInstruction);
    }

    @Override
    public void visitPhi(SSAPhiInstruction ssaPhiInstruction) {
        veriStatement = new PhiInstruction(ssaPhiInstruction);
    }

    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) {
        veriStatement = SkipStmt.skip;
    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
        canVeritest = false;
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {
        canVeritest = false;
    }

    public static StaticRegionException sre = new StaticRegionException("Untranslatable instruction in SSAToStatIVisitor");

    public static Stmt convert(SSAInstruction ssa) throws StaticRegionException {
        SSAToStatIVisitor visitor = new SSAToStatIVisitor();
        ssa.visit(visitor);
        if (!visitor.canVeritest) { throw sre; }
        else return visitor.veriStatement;
    }
}

