
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * SSA instruction that reads a field (i.e. getstatic or getfield).
 */
public class SSAGetInstruction implements VeriExpression {
    private final Var result;
    private final int iindex;
    private final VeriExpression ref;
    private final FieldReference field;
    private final boolean isStatic;

    protected SSAGetInstruction(int iindex, Var result, VeriExpression ref, FieldReference field, boolean isStatic) {
        this.iindex = iindex;
        this.result = result;
        this.ref = ref;
        this.field = field;
        this.isStatic = isStatic;
    }

    public Var getResult() {
        return result;
    }

    public int getIindex() {
        return iindex;
    }

    public VeriExpression getRef() {
        return ref;
    }

    public FieldReference getField() {
        return field;
    }

    public boolean isStatic() {
        return isStatic;
    }

    @Override
    public String toString() {
        if (isStatic()) {
            return result + " = getstatic " + getField();
        } else {
            return result + " = getfield " + getField() + " "
                    + getRef();
        }
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitGetInstruction(this);
    }
}
