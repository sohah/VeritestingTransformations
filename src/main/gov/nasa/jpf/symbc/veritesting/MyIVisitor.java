package gov.nasa.jpf.symbc.veritesting;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrikeBT.IInvokeInstruction;
import com.ibm.wala.shrikeBT.IShiftInstruction;
import com.ibm.wala.ssa.*;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.strings.Atom;
import gov.nasa.jpf.symbc.bytecode.INVOKEVIRTUAL;
import za.ac.sun.cs.green.expr.Expression;

import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Operation.Operator;

import java.util.ArrayList;

public class MyIVisitor implements SSAInstruction.IVisitor {
    private final int thenUseNum;
    private final int elseUseNum;
    private final boolean isMeetVisitor;
    boolean isPhiInstruction = false;
    VarUtil varUtil;
    SSAInstruction lastInstruction;
    private Expression phiExprThen;
    private Expression phiExprElse;
    private Expression phiExprLHS;
    private String invokeVirtualClassName;
    private boolean isInvokeVirtual = false;

    public boolean isExitNode() {
        return isExitNode;
    }
    private boolean isExitNode = false;

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

    private Expression SPFExpr;

    public MyIVisitor(VarUtil _varUtil, int _thenUseNum, int _elseUseNum, boolean _isMeetVisitor) {
        varUtil = _varUtil;
        thenUseNum = _thenUseNum;
        elseUseNum = _elseUseNum;
        isMeetVisitor = _isMeetVisitor;
        //SPFExpr = new String();
    }

    @Override
    public void visitGoto(SSAGotoInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAGotoInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = true;
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAArrayLoadInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAArrayStoreInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSABinaryOpInstruction = " + instruction);
        lastInstruction = instruction;
        assert(instruction.getNumberOfUses()==2);
        assert(instruction.getNumberOfDefs()==1);
        assert(instruction.mayBeIntegerOp()==true);
        int lhs = instruction.getDef();
        int operand1 = instruction.getUse(0);
        int operand2 = instruction.getUse(1);
        //variables written to in a veritesting region will always become intermediates because they will be
        //phi'd at the end of the region or be written into a class field later
        Expression lhsExpr = varUtil.makeIntermediateVar(lhs);
        Expression operand1Expr = varUtil.addVal(operand1);
        Expression operand2Expr = varUtil.addVal(operand2);

        assert(!varUtil.isConstant(lhs));
        Operator operator = null;
        if(instruction.getOperator() instanceof IBinaryOpInstruction.Operator) {
            switch((IBinaryOpInstruction.Operator) instruction.getOperator()) {
                case ADD: operator = Operator.ADD; break;
                case SUB: operator = Operator.SUB; break;
                case MUL: operator = Operator.MUL; break;
                case DIV: operator = Operator.DIV; break;
                case REM: operator = Operator.MOD; break;
                case AND: operator = Operator.BIT_AND; break;
                case OR: operator = Operator.BIT_OR; break;
                case XOR: operator = Operator.BIT_XOR; break;
                default:
                    System.out.println("unsupported operator (" + instruction.getOperator() + ") in SSABinaryOpInstruction");
                    assert(false);
            }
        } else if(instruction.getOperator() instanceof IShiftInstruction.Operator) {
            switch((IShiftInstruction.Operator) instruction.getOperator()) {
                case SHL: operator = Operator.SHIFTL; break;
                case SHR: operator = Operator.SHIFTR; break;
                case USHR: operator = Operator.SHIFTUR; break;
                default:
                    System.out.println("unsupported operator (" + instruction.getOperator() + ") in SSABinaryOpInstruction");
                    assert(false);
            }
        } else {
            System.out.println("unknown type of operator (" + instruction.getOperator() + ") in SSABinaryOpInstruction");
            assert(false);
        }
        SPFExpr =
                new Operation(Operator.EQ, lhsExpr,
                        new Operation(operator, operand1Expr, operand2Expr));
        canVeritest = true;
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAUnaryOpInstruction = " + instruction);
        lastInstruction = instruction;
        //TODO: make SPFExpr
        canVeritest = false;
    }

    @Override
    public void visitConversion(SSAConversionInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAConversionInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitComparison(SSAComparisonInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAComparisonInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction instruction) {
        if(isMeetVisitor) return;
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
        if(isMeetVisitor) return;
        System.out.println("SSASwitchInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitReturn(SSAReturnInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAReturnInstruction = " + instruction);
        //we can only handle a return value not associated with an object
        if (instruction.getNumberOfUses() > 1) {
            canVeritest = false;
            return;
        }
        isExitNode = true;
        varUtil.addRetValHole(instruction.getUse(0));
        lastInstruction = instruction;
        canVeritest = true;
    }

    @Override
    public void visitGet(SSAGetInstruction instruction) {
        lastInstruction = instruction;
        if(isMeetVisitor) return;
        System.out.println("SSAGetInstruction = " + instruction);
        if(instruction.isStatic()) {
            canVeritest = false;
            return;
        }
        assert(instruction.getNumberOfDefs()==1);
        assert(instruction.getNumberOfUses()==1);
        FieldReference fieldReference = instruction.getDeclaredField();
        Atom declaringClass = fieldReference.getDeclaringClass().getName().getClassName();
        Atom fieldName = fieldReference.getName();
        System.out.println("declaringClass = " + declaringClass + ", methodName = " + fieldName);
        int use = instruction.getUse(0);
        int def = instruction.getDef(0);
        varUtil.addFieldVal(def, use, declaringClass.toString(), fieldName.toString(),
                HoleExpression.HoleType.FIELD_INPUT);

        canVeritest = true;
    }

    @Override
    public void visitPut(SSAPutInstruction instruction) {
        lastInstruction = instruction;
        if(isMeetVisitor) return;
        System.out.println("SSAPutInstruction = " + instruction);
        if(instruction.isStatic()) {
            assert(instruction.getNumberOfUses()==1);
            assert(instruction.getNumberOfDefs()==0);
        } else {
            assert (instruction.getNumberOfUses() == 2);
            assert (instruction.getNumberOfDefs() == 0);
        }
        int objRef = instruction.getRef();
        int defVal = instruction.getVal();
        FieldReference fieldReference = instruction.getDeclaredField();
        Atom declaringClass = fieldReference.getDeclaringClass().getName().getClassName();
        Atom fieldName = fieldReference.getName();
        varUtil.addFieldVal(defVal, objRef, declaringClass.toString(), fieldName.toString(),
                HoleExpression.HoleType.FIELD_OUTPUT);
        canVeritest = true;
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAInvokeInstruction = " + instruction);
        lastInstruction = instruction;
        MethodReference methodReference = instruction.getDeclaredTarget();
        CallSiteReference site = instruction.getCallSite();
        //Only adding support for invokeVirtual statements
        if(site.getInvocationCode() != IInvokeInstruction.Dispatch.VIRTUAL) {
            canVeritest = false;
            return;
        }
        assert(instruction.getNumberOfUses() == instruction.getNumberOfParameters());
        Atom declaringClass = methodReference.getDeclaringClass().getName().getClassName();
        Atom methodName = methodReference.getName();
        int defVal = instruction.getDef(); // represents the return value
        ArrayList<Expression> paramList = new ArrayList<>();
        for(int i=0; i < instruction.getNumberOfParameters(); i++) {
            paramList.add(varUtil.addVal(instruction.getUse(i)));
        }
        InvokeVirtualInfo virtualInfo = new InvokeVirtualInfo();
        virtualInfo.setDefVal(defVal);
        virtualInfo.setClassName(declaringClass.toString());
        virtualInfo.setMethodName(methodName.toString());
        virtualInfo.setParamList(paramList);
        varUtil.addInvokeVirtualHole(virtualInfo);
        invokeVirtualClassName = declaringClass.toString();
        isInvokeVirtual = true;
        canVeritest = true;
    }

    @Override
    public void visitNew(SSANewInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSANewInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAArrayLengthInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitThrow(SSAThrowInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAThrowInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAMonitorInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSACheckCastInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction instruction) {
        if(isMeetVisitor) return;
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
        phiExprThen = varUtil.addVal(instruction.getUse(thenUseNum));
        phiExprElse = varUtil.addVal(instruction.getUse(elseUseNum));
        phiExprLHS = varUtil.addDefVal(instruction.getDef(0));
        assert(!(phiExprLHS instanceof HoleExpression && !((HoleExpression)phiExprLHS).isHole()));
        assert(varUtil.ir.getSymbolTable().isConstant(instruction.getDef(0)) == false);
        //while other instructions may also update local variables, those should always become intermediate variables
    }

    @Override
    public void visitPi(SSAPiInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAPiInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSAGetCaughtExceptionInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction instruction) {
        if(isMeetVisitor) return;
        System.out.println("SSALoadMetadataInstruction = " + instruction);
        lastInstruction = instruction;
        canVeritest = false;
    }

    public Expression getSPFExpr() {
        return SPFExpr;
    }

    public String getLastInstruction() {
        return lastInstruction.toString();
    }

    public Expression getPhiExprSPF(Expression thenPLAssignSPF,
                                    Expression elsePLAssignSPF) {
        assert(phiExprThen != null);
        assert(phiExprElse != null);
        assert(phiExprLHS != null);
        // (pathLabel == 1 && lhs == phiExprThen) || (pathLabel == 2 && lhs == phiExprElse)
        Operation thenExpr =
                new Operation(Operator.EQ, phiExprLHS, phiExprThen);
        Operation elseExpr =
                new Operation(Operator.EQ, phiExprLHS, phiExprElse);
        return new Operation(Operator.OR,
                new Operation(Operator.AND, thenPLAssignSPF, thenExpr),
                new Operation(Operator.AND, elsePLAssignSPF, elseExpr)
        );
    }

    public boolean hasPhiExpr() {
        return phiExprThen != null && phiExprElse != null && phiExprLHS != null;
    }

    public String getInvokeVirtualClassName() {
        return invokeVirtualClassName;
    }

    public boolean isInvokeVirtual() {
        return isInvokeVirtual;
    }
}
