
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * An instruction which converts a value of one primitive type into another primitive type.
 */
public class SSAConversionInstruction implements VeriExpression {
    private final Var result;

    private final VeriExpression val;

    private final TypeReference fromType;

    private final TypeReference toType;

    private final int iindex;

    protected SSAConversionInstruction(Var result, VeriExpression val, TypeReference fromType, TypeReference toType, int iindex) {
        this.result = result;
        this.val = val;
        this.fromType = fromType;
        this.toType = toType;
        this.iindex = iindex;
    }


    public int getIindex() {
        return iindex;
    }

    public TypeReference getToType() {
        return toType;
    }

    public TypeReference getFromType() {
        return fromType;
    }

    public VeriExpression getVal() {
        return val;
    }

    public Var getResult() {
        return result;
    }

    @Override
    public String toString() {
        return result + " = conversion(" + toType.getName() + ") " + val;
    }


    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitConversionSSA(this);
        ;
    }


}