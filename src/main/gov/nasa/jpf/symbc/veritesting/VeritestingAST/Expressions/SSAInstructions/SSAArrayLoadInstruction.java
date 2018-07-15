
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;


public class SSAArrayLoadInstruction implements VeriExpression {
    private final int iindex;
    private final Var result;
    private final VeriExpression arrayref;
    private final int index;
    private final TypeReference elementType;

    protected SSAArrayLoadInstruction(int iindex, Var result, VeriExpression arrayref, int index, TypeReference elementType) {
        this.iindex = iindex;
        this.result = result;
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
    }


    public Var getResult() {
        return result;
    }

    public VeriExpression getArrayref() {
        return arrayref;
    }

    public int getIndex() {
        return index;
    }

    public TypeReference getElementType() {
        return elementType;
    }


    public int getIindex() {
        return iindex;
    }

    @Override
    public String toString() {
        return result + " = arrayload " + getArrayref() + "[" + getIndex() + "]";
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitArrayLoadSSA(this);
    }

}
