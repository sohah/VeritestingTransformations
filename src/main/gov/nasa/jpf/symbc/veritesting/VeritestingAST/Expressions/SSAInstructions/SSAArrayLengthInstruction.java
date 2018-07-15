
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;


import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * SSA instruction representing v_x := arraylength v_y
 */
public class SSAArrayLengthInstruction implements VeriExpression {
    private final Var result;
    private final VeriExpression arrayref;
    int iindex;

    protected SSAArrayLengthInstruction(int iindex, Var result, VeriExpression arrayref) {
        this.result = result;
        this.arrayref = arrayref;
        this.iindex = iindex;
    }


    public Var getResult() {
        return result;
    }

    public VeriExpression getArrayRef() {
        return arrayref;
    }


    public VeriExpression getArrayref() {
        return arrayref;
    }

    public int getIindex() {
        return iindex;
    }

    public boolean isPEI() {
        return true;
    }

    @Override
    public String toString() {
        return result + " = arraylength " + arrayref;
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitArrayLengthVeriSSA(this);
    }
}
