package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSAConversionInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public class ConversionInstruction extends Instruction {

    public final VarExpr result;
    public final Expr val;
    public final TypeReference fromType;
    public final TypeReference toType;

    public ConversionInstruction(SSAConversionInstruction ins, VarExpr result, Expr val, TypeReference fromType, TypeReference toType) {
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
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
