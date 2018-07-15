
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.shrikeBT.BinaryOpInstruction;
import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

public class SSABinaryOpInstruction implements VeriExpression {

    /**
     * Might this instruction represent integer arithmetic?
     */
    private final boolean mayBeInteger;
    private final int iindex;
    private final IBinaryOpInstruction.IOperator operator;
    private final Var result;
    private final VeriExpression val1;
    private final VeriExpression val2;

    protected SSABinaryOpInstruction(int iindex, IBinaryOpInstruction.IOperator operator, Var result, VeriExpression val1, VeriExpression val2, boolean mayBeInteger) {
        this.iindex = iindex;
        this.operator = operator;
        this.result = result;
        this.val1 = val1;
        this.val2 = val2;
        this.mayBeInteger = mayBeInteger;
    }


    public IBinaryOpInstruction.IOperator getOperator() {
        return operator;
    }

    public Var getResult() {
        return result;
    }

    public VeriExpression getVal1() {
        return val1;
    }

    public VeriExpression getVal2() {
        return val2;
    }


    public int getIindex() {
        return iindex;
    }

    public boolean isPEI() {
        return mayBeInteger && (operator == BinaryOpInstruction.Operator.DIV || operator == BinaryOpInstruction.Operator.REM);
    }


    @Override
    public String toString() {
        return result + " = binaryop(" + operator + ") " + val1 + " , " + val2;
    }


    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitBinaryOpSSA(this);
    }
}
