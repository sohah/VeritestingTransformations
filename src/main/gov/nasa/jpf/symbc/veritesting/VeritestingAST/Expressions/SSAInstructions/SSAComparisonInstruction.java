
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.shrikeBT.IComparisonInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * SSA Instruction for comparisons between floats, longs and doubles
 */
public class SSAComparisonInstruction implements VeriExpression {
    private final Var result;

    private final VeriExpression val1;

    private final VeriExpression val2;

    private final IComparisonInstruction.Operator operator;
    private final int iindex;

    public SSAComparisonInstruction(int iindex, Var result, VeriExpression val1, VeriExpression val2, IComparisonInstruction.Operator operator) {
        this.result = result;
        this.val1 = val1;
        this.val2 = val2;
        this.operator = operator;
        this.iindex = iindex;
    }

    public Var getResult() {
        return result;
    }

    public int getIindex() {
        return iindex;
    }

    public VeriExpression getVal1() {
        return val1;
    }

    public VeriExpression getVal2() {
        return val2;
    }


    public IComparisonInstruction.Operator getOperator() {
        return operator;
    }

    public String toString() {
        return result + " = compare " + val1 + "," + val2 + " opcode=" + operator;
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitComparisonSSA(this);
    }


}
