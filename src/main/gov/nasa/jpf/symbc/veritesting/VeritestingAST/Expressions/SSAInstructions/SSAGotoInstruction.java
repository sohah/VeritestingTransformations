
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * Unconditional branch instruction for SSA form.
 */
public class SSAGotoInstruction implements VeriExpression {
    private final int iindex;
    private final int target;

    public SSAGotoInstruction(int iindex, int target) {
        this.iindex = iindex;
        this.target = target;
    }

    public int getIindex() {
        return iindex;
    }

    public int getTarget() {
        return this.target;
    }


    @Override
    public String toString() {
        return "goto (from iindex= " + this.iindex + " to iindex = " + this.target + ")";
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitGoToSSA(this);
    }
}
