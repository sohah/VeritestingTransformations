package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAConversionInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ConversionInstruction extends Instruction {

    public final VarExpr result;
    public final Expression val;
    public final TypeReference fromType;
    public final TypeReference toType;

    public ConversionInstruction(SSAConversionInstruction ins, VarExpr result, Expression val, TypeReference fromType, TypeReference toType) {
        super(ins);
        this.result = result;
        this.val = val;
        this.fromType = fromType;
        this.toType = toType;
    }

    public ConversionInstruction(SSAConversionInstruction ins) {
        super(ins);
        result = new WalaVarExpr(ins.getDef());
        val = new WalaVarExpr(ins.getUse(0));
        fromType = ins.getFromType();
        toType = ins.getToType();
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
