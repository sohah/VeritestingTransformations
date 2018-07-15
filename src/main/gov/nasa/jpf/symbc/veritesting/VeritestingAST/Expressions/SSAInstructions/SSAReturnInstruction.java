
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * A return instruction.
 */
public class SSAReturnInstruction implements VeriExpression {

    /**
     * value number of the result. By convention result == -1 means returns void.
     */
    private final Var result;
    private final int iindex;
    private final boolean isVoid;

    private final boolean isPrimitive;

    public SSAReturnInstruction(int iindex, Var result, boolean isPrimitive, boolean isVoid) {
        this.iindex = iindex;
        this.result = result;
        this.isPrimitive = isPrimitive;
        this.isVoid = isVoid;
    }

    public boolean returnsPrimitiveType() {
        return isPrimitive;
    }

    public Var getResult() {
        return result;
    }

    public boolean isVoid() {
        return isVoid;
    }

    public int getIindex() {
        return iindex;
    }

    @Override
    public String toString() {
        if (isVoid) {
            return "return";
        } else {
            return "return " + result;
        }
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitReturnInstruction(this);
    }


}
