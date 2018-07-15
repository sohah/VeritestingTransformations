package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public class InstanceOfInstruction extends Instruction {

    public final VarExpr result;
    public final Expr val;
    public final TypeReference checkedType;

    public InstanceOfInstruction(SSAInstanceofInstruction ins, VarExpr result, Expr val, TypeReference checkedType) {
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

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
