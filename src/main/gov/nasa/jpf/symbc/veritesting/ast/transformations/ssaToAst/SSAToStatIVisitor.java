package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;



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
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLoadInstruction(ssaArrayLoadInstruction);
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ssaArrayStoreInstruction) {
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayStoreInstruction(ssaArrayStoreInstruction);
    }

    private Operation.Operator translateBinaryOp(IBinaryOpInstruction.Operator op) {
        switch (op) {
            case ADD: return Operation.Operator.ADD;
            case SUB: return Operation.Operator.SUB;
            case MUL: return Operation.Operator.MUL;
            case DIV: return Operation.Operator.DIV;
            case REM: return Operation.Operator.MOD;
            case AND: return Operation.Operator.AND;
            case OR: return Operation.Operator.OR;
            case XOR: return Operation.Operator.NOTEQUALS;
        }
        throw new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateBinaryOp");
    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ssa) {
        Expression lhs = new WalaVarExpr(ssa.getDef());
        Operation.Operator op = translateBinaryOp((IBinaryOpInstruction.Operator)ssa.getOperator());
        Expression op1 = new WalaVarExpr(ssa.getUse(0));
        Expression op2 = new WalaVarExpr(ssa.getUse(1));
        Expression rhs = new Operation(op, op1, op2);
        Stmt s = new AssignmentStmt(lhs, rhs);
        veriStatement = s;
        /*veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                new Operation(
                        translateBinaryOp((IBinaryOpInstruction.Operator)ssa.getOperator()),
                        new WalaVarExpr(ssa.getUse(0)),
                        new WalaVarExpr(ssa.getUse(1))));*/
    }

    Operation.Operator translateUnaryOp(IUnaryOpInstruction.Operator op) {
        switch(op) {
            case NEG: return Operation.Operator.NEG;
        }
        throw new IllegalArgumentException("Unknown Operator: " + op.toString() + " in translateUnaryOp");
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ssa) {
        veriStatement = new AssignmentStmt(new WalaVarExpr(ssa.getDef()),
                new Operation(
                        translateUnaryOp((IUnaryOpInstruction.Operator)ssa.getOpcode()),
                                new WalaVarExpr(ssa.getUse(0)))
                );
    }

    /*
        MWW: casts in SPF involve object creation, so are beyond what we can support currently in
        Static regions.
     */
    @Override
    public void visitConversion(SSAConversionInstruction ssa) {
        canVeritest = false;
        // veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ConversionInstruction(ssa);
    }


    @Override
    public void visitComparison(SSAComparisonInstruction ssa) {
        Expression expr;
        Expression condlhs = new WalaVarExpr(ssa.getUse(0));
        Expression condrhs = new WalaVarExpr(ssa.getUse(1));
        Operation.Operator condOp =
                (ssa.getOperator() == IComparisonInstruction.Operator.CMP ||
                        ssa.getOperator() == IComparisonInstruction.Operator.CMPG) ?
                        Operation.Operator.GT :
                        Operation.Operator.LT ;
        Expression rhs = new IfThenElseExpr(
                new Operation(condOp, condlhs, condrhs),
                Operation.ONE,
                new IfThenElseExpr(
                        new Operation(Operation.Operator.EQ, condlhs, condrhs),
                        Operation.ZERO,
                        new IntConstant(-1)));


        veriStatement =
                new AssignmentStmt(new WalaVarExpr(ssa.getDef()), rhs);
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ssa) {
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
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.ArrayLengthInstruction(ssaArrayLengthInstruction);
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
        veriStatement = new gov.nasa.jpf.symbc.veritesting.ast.def.PhiInstruction(ssaPhiInstruction);
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

