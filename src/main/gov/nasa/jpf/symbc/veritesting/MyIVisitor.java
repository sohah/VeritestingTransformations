package gov.nasa.jpf.symbc.veritesting;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.ssa.*;


public class MyIVisitor implements SSAInstruction.IVisitor {
    private final int thenUseNum;
    private final int elseUseNum;
    boolean isPhiInstruction = false;
    VarUtil varUtil;
    SSAInstruction lastInstruction;
    private String phiExprThen;
    private String phiExprElse;
    private String phiExprLHS;

    public boolean canVeritest() {
        return canVeritest;
    }

    private boolean canVeritest;

    /*public String getIfExprStr_SPF() {
        return ifExprStr_SPF;
    }

    public String getIfNotExprStr_SPF() {
        return ifNotExprStr_SPF;
    }

    private String ifExprStr_SPF, ifNotExprStr_SPF;*/

    private String SPFExpr;

    public MyIVisitor(VarUtil _varUtil, int _thenUseNum, int _elseUseNum) {
        varUtil = _varUtil;
        thenUseNum = _thenUseNum;
        elseUseNum = _elseUseNum;
        SPFExpr = new String();
    }

    @Override
    public void visitGoto(SSAGotoInstruction instruction) {
        System.out.println("SSAGotoInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = true;
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction instruction) {
        System.out.println("SSAArrayLoadInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction instruction) {
        System.out.println("SSAArrayStoreInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction instruction) {
        System.out.println("SSABinaryOpInstruction = " + instruction);
        lastInstruction = instruction;
        assert(instruction.getNumberOfUses()==2);
        assert(instruction.getNumberOfDefs()==1);
        assert(instruction.mayBeIntegerOp()==true);
        int lhs = instruction.getDef();
        int operand1 = instruction.getUse(0);
        int operand2 = instruction.getUse(1);
        varUtil.addVal(operand1);
        varUtil.addVal(operand2);
        varUtil.addIntermediateVar(lhs);
        String operand1String = new String("v" + operand1), operand2String = new String("v" + operand2);
        String lhsString = new String("v" + lhs);
        if(varUtil.isConstant(operand1))
            operand1String = new String("new IntegerConstant(" + varUtil.getConstant(operand1) + ")");
        if(varUtil.isConstant(operand2))
            operand2String = new String("new IntegerConstant(" + varUtil.getConstant(operand2) + ")");
        assert(!varUtil.isConstant(lhs));
        String operatorString = new String();
        // ADD, SUB, MUL, DIV, REM, AND, OR, XOR
        switch((IBinaryOpInstruction.Operator) instruction.getOperator()) {
            case ADD: operatorString = "PLUS"; break;
            case SUB: operatorString = "MINUS"; break;
            case MUL: operatorString = "MINUS"; break;
            case DIV: operatorString = "MUL"; break;
            case REM: operatorString = "REM"; break;
            case AND: operatorString = "AND"; break;
            case OR: operatorString = "OR"; break;
            case XOR: operatorString = "XOR"; break;
            default:
                System.out.println("unsupported operator (" + instruction.getOperator() + ") in SSABinaryOpInstruction");
                assert(false);
        }
        SPFExpr = varUtil.nCNLIE + "(" + lhsString + ", EQ, " +
                varUtil.nCNLIE + "(" + operand1String + ", " + operatorString + ", " + operand2String + ") )";
        canVeritest = true;
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction instruction) {
        System.out.println("SSAUnaryOpInstruction = " + instruction);
        lastInstruction = instruction;
        //TODO: make SPFExpr
        canVeritest = false;
    }

    @Override
    public void visitConversion(SSAConversionInstruction instruction) {
        System.out.println("SSAConversionInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitComparison(SSAComparisonInstruction instruction) {
        System.out.println("SSAComparisonInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction instruction) {
        System.out.println("SSAConditionalBranchInstruction = " + instruction);
        lastInstruction = instruction;
        if(!instruction.isIntegerComparison()) {
            System.out.println("can only veritest with integer comparison-containing conditional branch instructions\n");
            canVeritest=false;
            return;
        }
        /*IConditionalBranchInstruction.IOperator op = instruction.getOperator();
        String opString = new String();
        String opNotString = new String();
        if (op.equals(IConditionalBranchInstruction.Operator.NE)) {
            opString = "NE";
            opNotString = "EQ";
        } else if (op.equals(IConditionalBranchInstruction.Operator.EQ)) {
            opString = "EQ";
            opNotString = "NE";
        } else if (op.equals(IConditionalBranchInstruction.Operator.LE)) {
            opString = "LE";
            opNotString = "GT";
        } else if (op.equals(IConditionalBranchInstruction.Operator.LT)) {
            opString = "LT";
            opNotString = "GE";
        } else if (op.equals(IConditionalBranchInstruction.Operator.GE)) {
            opString = "GE";
            opNotString = "LT";
        } else if (op.equals(IConditionalBranchInstruction.Operator.GT)) {
            opString = "GT";
            opNotString = "LE";
        }
        ifExprStr_SPF = "new ComplexNonLinearIntegerExpression(" +
                varUtil.getValueString(instruction.getUse(0)) + ", " + opString + ", " +
                varUtil.getValueString(instruction.getUse(1)) + ")";
        ifNotExprStr_SPF = "new ComplexNonLinearIntegerExpression(" +
                varUtil.getValueString(instruction.getUse(0)) + ", " + opNotString + ", " +
                varUtil.getValueString(instruction.getUse(1)) + ")";
        // get their definitions if they are intermediates and construct them
        // using symbolic formulas
        varUtil.addConditionalVal(instruction.getUse(0));
        varUtil.addConditionalVal(instruction.getUse(1));*/
        canVeritest=true;
    }

    @Override
    public void visitSwitch(SSASwitchInstruction instruction) {
        System.out.println("SSASwitchInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitReturn(SSAReturnInstruction instruction) {
        System.out.println("SSAReturnInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitGet(SSAGetInstruction instruction) {
        System.out.println("SSAGetInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitPut(SSAPutInstruction instruction) {
        System.out.println("SSAPutInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction instruction) {
        System.out.println("SSAInvokeInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitNew(SSANewInstruction instruction) {
        System.out.println("SSANewInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction instruction) {
        System.out.println("SSAArrayLengthInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitThrow(SSAThrowInstruction instruction) {
        System.out.println("SSAThrowInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction instruction) {
        System.out.println("SSAMonitorInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction instruction) {
        System.out.println("SSACheckCastInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction instruction) {
        System.out.println("SSAInstanceofInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitPhi(SSAPhiInstruction instruction) {
        isPhiInstruction = true;
        System.out.println("SSAPhiInstruction = " + instruction);
        lastInstruction = instruction;
        assert(instruction.getNumberOfUses()==2);
        assert(instruction.getNumberOfDefs()==1);

        assert(thenUseNum != -1);
        assert(elseUseNum != -1);
        phiExprThen = varUtil.getValueString(instruction.getUse(thenUseNum));
        phiExprElse = varUtil.getValueString(instruction.getUse(elseUseNum));
        phiExprLHS = varUtil.getValueString(instruction.getDef(0));
        assert(varUtil.ir.getSymbolTable().isConstant(instruction.getDef(0)) == false);
        varUtil.addVal(instruction.getUse(0));
        varUtil.addVal(instruction.getUse(1));
        //while other instructions may also update local variables, those should always become intermediate variables
        varUtil.addDefVal(instruction.getDef(0));
    }

    @Override
    public void visitPi(SSAPiInstruction instruction) {
        System.out.println("SSAPiInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction instruction) {
        System.out.println("SSAGetCaughtExceptionInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction instruction) {
        System.out.println("SSALoadMetadataInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    public String getSPFExpr() {
        return SPFExpr;
    }

    public String getLastInstruction() {
        return lastInstruction.toString();
    }

    public String getPhiExprSPF(String thenPLAssignSPF, String elsePLAssignSPF) {
        assert(phiExprThen != null && phiExprThen != "");
        assert(phiExprElse != null && phiExprElse != "");
        assert(phiExprLHS != null && phiExprLHS != "");
        String phiExprThen_s = StringUtil.nCNLIE + phiExprLHS + ", EQ, " + phiExprThen + ")";
        String phiExprElse_s = StringUtil.nCNLIE + phiExprLHS + ", EQ, " + phiExprElse + ")";
        // (pathLabel == 1 && lhs == phiExprThen) || (pathLabel == 2 && lhs == phiExprElse)
        return StringUtil.SPFLogicalOr(
                StringUtil.SPFLogicalAnd( thenPLAssignSPF,
                        phiExprThen_s),
                StringUtil.SPFLogicalAnd( elsePLAssignSPF,
                        phiExprElse_s
                ));
    }

}
