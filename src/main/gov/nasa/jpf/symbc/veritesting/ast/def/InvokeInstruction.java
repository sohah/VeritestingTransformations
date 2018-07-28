package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInvokeInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Arrays;

public class InvokeInstruction extends Instruction {
    public final Expression [] result;
    public final Expression [] params;

    public InvokeInstruction(SSAInvokeInstruction ins, Expression [] result, Expression[] params)
    {
        super(ins);
        this.result = result;

        //SH: this part is mainly to create params in InovkeInstructions that contains non null params, since wala's instruction can have null
        // paramaters.
        /*int nonNullCount = 0;
        for(int i = 0; i < params.length; i++)
            if(params[i] != null)
                ++nonNullCount;

        this.params = new Expression [nonNullCount];

        for(int i = 0; i < nonNullCount; i++)
            if(params[i] != null)
                this.params[i] = params[i];*/
        this.params = params;
    }

    public InvokeInstruction(SSAInvokeInstruction ins)
    {
        super(ins);
        result = new Expression [ins.getNumberOfReturnValues()];
        for (int i = 0; i < ins.getNumberOfReturnValues(); i++) {
            result[i] = new WalaVarExpr(ins.getReturnValue(i));
        }
        this.params = new Expression[ins.getNumberOfParameters()];
        for (int i = 0; i < ins.getNumberOfParameters(); i++) {
            params[i] = new WalaVarExpr(ins.getUse(i));
        }
    }

    public SSAInvokeInstruction getOriginal() {
        return (SSAInvokeInstruction)original;
    }


    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }


    @Override
    public String toString() {
        return "\n invoke " + Arrays.toString(params) + "=" + Arrays.toString(result);
    }
}
