
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.shrikeBT.IConditionalBranchInstruction.IOperator;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * A conditional branch instruction, which tests two values according to some {@link IOperator}.
 */
public class SSAConditionalBranchInstruction implements VeriExpression {
    private final IConditionalBranchInstruction.IOperator operator;

    private final VeriExpression val1;

    private final VeriExpression val2;

    private final TypeReference type;

    final private int target;

    final private int iindex;

    public SSAConditionalBranchInstruction(int iindex, IOperator operator, VeriExpression val1, VeriExpression val2, TypeReference type, int target) {
        this.operator = operator;
        this.val1 = val1;
        this.val2 = val2;
        this.type = type;
        this.target = target;
        this.iindex = iindex;
    }


    public int getTarget() {
        return target;
    }

    public int getIindex() {
        return iindex;
    }

    public TypeReference getType() {
        return type;
    }

    public VeriExpression getVal2() {
        return val2;
    }

    public VeriExpression getVal1() {
        return val1;
    }

    public IConditionalBranchInstruction.IOperator getOperator() {
        return operator;
    }


    public boolean isObjectComparison() {
        return type.isReferenceType();
    }

    public boolean isIntegerComparison() {
        return type == TypeReference.Int;
    }

    public void visit(VeriExpressionVisitor v) {
        v.visitConditionalBranchSSA(this);
    }

    public String toString() {
        return "conditional branch(" + operator + ", to iindex=" + target + ") " + val1 + "," + val2;
    }
}
