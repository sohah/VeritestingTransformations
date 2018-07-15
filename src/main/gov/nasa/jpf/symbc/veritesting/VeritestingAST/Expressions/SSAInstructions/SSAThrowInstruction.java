
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.ssa.SSAAbstractThrowInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * An instruction which unconditionally throws an exception
 */
public class SSAThrowInstruction implements VeriExpression {

    private final int iindex;
    private final int exception;


    protected SSAThrowInstruction(int iindex, int exception) {
        this.iindex = iindex;
        this.exception = exception;
    }

    public int getIindex() {
        return iindex;
    }

    public int getException() {
        return exception;
    }

    @Override
    public String toString() {
        return iindex + " throw( " + exception + ")";
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitThrowSSA(this);
    }
}
