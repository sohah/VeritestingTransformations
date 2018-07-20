package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAToStatIVisitor;

import java.util.HashMap;


//SH: This visitor fills the stack slots for wala vars.


public class StackSlotIVisitor implements SSAInstruction.IVisitor {
    public final HashMap<Integer, int[]> stackSlotMap = new HashMap<>();
    private IR ir;

    public StackSlotIVisitor(IR ir) { this.ir = ir; }

    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) {
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ins) {
        populateVars(ins, ins.getArrayRef());
        populateVars(ins, ins.getIndex());
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ins) {
        populateVars(ins, ins.getArrayRef());
        populateVars(ins, ins.getIndex());
        populateVars(ins, ins.getDef());

    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getUse(1));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ins) {
        populateVars(ins, ins.getDef());
        populateVars(ins, ins.getUse(0));
    }

    @Override
    public void visitConversion(SSAConversionInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());

    }

    @Override
    public void visitComparison(SSAComparisonInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getUse(1));
        populateVars(ins, ins.getDef());

    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getUse(1));
    }

    @Override
    public void visitSwitch(SSASwitchInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitReturn(SSAReturnInstruction ins) {
        populateVars(ins, ins.getUse(0));
    }

    @Override
    public void visitGet(SSAGetInstruction ins) {
        populateVars(ins, ins.getRef());
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitPut(SSAPutInstruction ins) {
        if (ins.isStatic())
            populateVars(ins, ins.getUse(0));
        else
            populateVars(ins, ins.getUse(1));
        populateVars(ins, ins.getRef());
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction ins) {

        for (int i = 0; i < ins.getNumberOfParameters(); i++) {
            populateVars(ins, ins.getUse(i));
        }

        for (int i = 0; i < ins.getNumberOfReturnValues(); i++) {
            populateVars(ins, ins.getReturnValue(i));
        }    }

    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ins) {
        populateVars(ins, ins.getArrayRef());
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {

    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitPhi(SSAPhiInstruction ins) {
        for (int i = 0; i < ins.getNumberOfUses(); i++) {
            populateVars(ins, ins.getUse(i));
        }
    }

    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) {

    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {

    }

// SH: Used only to get the stack slot of "use" vars, which are either already defined in a previous "def" and so it will
// be in the stackSlotMap otherwise look into wala, because this can be inputs.

    public void populateVars(SSAInstruction ins, int var) {
        int iindex = ins.iindex;
        if (!(ins instanceof  SSAPhiInstruction) && ((stackSlotMap.get(var) == null)|| (stackSlotMap.get(var)[0] == -1))) {
            int[] localNumbers = ir.findLocalsForValueNumber(iindex, var);
            if (localNumbers != null)
                stackSlotMap.put(var, localNumbers);
            }
    }
}
