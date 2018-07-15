package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public class ReturnInstruction extends Instruction {

    public final Expr rhs;

    public ReturnInstruction(SSAReturnInstruction ins, Expr rhs) {
        super(ins);
        this.rhs = rhs;
    }

    public ReturnInstruction(SSAReturnInstruction ins) {
        super(ins);
        rhs = new WalaVarExpr(ins.getUse(0));
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
