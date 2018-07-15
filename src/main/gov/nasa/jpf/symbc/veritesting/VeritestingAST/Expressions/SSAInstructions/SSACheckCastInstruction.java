
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInstructionFactory;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

public class SSACheckCastInstruction implements VeriExpression {

    /**
     * A new value number def'fed by this instruction when the type check succeeds.
     */
    private final Var result;

    /**
     * The value being checked by this instruction
     */
    private final VeriExpression val;

    /**
     * The types for which this instruction checks; the assignment succeeds if the val is a subtype of one of these types
     */
    private final TypeReference[] declaredResultTypes;

    /**
     * whether the type test throws an exception
     */
    private final boolean isPEI;


    private final int iindex;

    protected SSACheckCastInstruction(int iindex, Var result, VeriExpression val, TypeReference[] types, boolean isPEI) {
        this.iindex = iindex;
        this.result = result;
        this.val = val;
        this.declaredResultTypes = types;
        this.isPEI = isPEI;
    }

    public TypeReference getDeclaredResultType() {
        assert declaredResultTypes.length == 1;
        return declaredResultTypes[0];
    }

    public TypeReference[] getDeclaredResultTypes() {
        return declaredResultTypes;
    }

    public Var getResult() {
        return result;
    }

    public VeriExpression getVal() {
        return val;
    }

    public int getIindex() {
        return iindex;
    }


    public boolean isPEI() {
        return isPEI;
    }


    @Override
    public String toString() {
        String s = super.toString();
        for (TypeReference t : declaredResultTypes) {
            s = s + " " + t;
        }
        return s;
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitCheckCastSSA(this);
    }

}