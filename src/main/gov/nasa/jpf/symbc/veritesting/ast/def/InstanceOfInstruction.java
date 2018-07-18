package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class InstanceOfInstruction extends Instruction {

    public final VarExpr result;
    public final Expression val;
    public final TypeReference checkedType;

    public InstanceOfInstruction(SSAInstanceofInstruction ins, VarExpr result, Expression val, TypeReference checkedType) {
        super(ins);
        this.result = result;
        this.val = val;
        this.checkedType = checkedType;
    }

    public InstanceOfInstruction(SSAInstanceofInstruction ins) {
        super(ins);
        result = new WalaVarExpr(ins.getDef());
        val = new WalaVarExpr(ins.getUse(0));
        checkedType = ins.getCheckedType();
    }

    public SSAInstanceofInstruction getOriginal() {
        return (SSAInstanceofInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
