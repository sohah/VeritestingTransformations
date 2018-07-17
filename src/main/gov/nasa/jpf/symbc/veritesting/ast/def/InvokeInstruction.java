package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInvokeInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class InvokeInstruction extends Instruction {
    public final VarExpr [] result;
    public final Expression [] params;

    public InvokeInstruction(SSAInvokeInstruction ins, VarExpr [] result, Expression[] params)
    {
        super(ins);
        this.result = result;
        this.params = params;
    }

    public SSAInvokeInstruction getOriginal() {
        return (SSAInvokeInstruction)original;
    }
    public InvokeInstruction(SSAInvokeInstruction ins)
    {
        super(ins);
        result = new VarExpr [ins.getNumberOfReturnValues()];
        for (int i = 0; i < ins.getNumberOfReturnValues(); i++) {
            result[i] = new WalaVarExpr(ins.getReturnValue(i));
        }
        this.params = new Expression[ins.getNumberOfParameters()];
        for (int i = 0; i < ins.getNumberOfParameters(); i++) {
            result[i] = new WalaVarExpr(ins.getUse(i));
        }
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
