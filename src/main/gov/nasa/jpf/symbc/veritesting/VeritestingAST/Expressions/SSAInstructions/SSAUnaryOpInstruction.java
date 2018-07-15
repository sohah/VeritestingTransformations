
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.SSAAbstractUnaryInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInstructionFactory;
import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * An SSA instruction for some unary operator.
 *
 * @see IUnaryOpInstruction for a list of operators
 */
public class SSAUnaryOpInstruction implements VeriExpression {

    private final int iindex;
    private final IUnaryOpInstruction.IOperator operator;
    private final Var result;
    private final VeriExpression val;

    public SSAUnaryOpInstruction(int iindex, IUnaryOpInstruction.IOperator operator, Var result, VeriExpression val) {

        this.iindex = iindex;
        this.operator = operator;
        this.result = result;
        this.val = val;
    }


    public int getIindex() {
        return iindex;
    }

    public IUnaryOpInstruction.IOperator getOpcode() {
        return operator;
    }

    public Var getResult() {
        return result;
    }

    public VeriExpression getVal() {
        return val;
    }

    @Override
    public String toString() {
        return result + " = " + operator + " " + val;
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitUnaryOpSSA(this);
    }


}
