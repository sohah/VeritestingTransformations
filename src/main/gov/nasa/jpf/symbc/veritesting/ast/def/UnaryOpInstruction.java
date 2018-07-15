package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class UnaryOpInstruction extends Instruction {

    public final VarExpr def;
    public final IUnaryOpInstruction.IOperator op;
    public final Expr rhs;

    public UnaryOpInstruction(SSAInstruction ins, VarExpr def, IUnaryOpInstruction.IOperator op, Expr rhs) {
        super(ins);
        this.def = def;
        this.op = op;
        this.rhs = rhs;
    }

    public UnaryOpInstruction(SSAUnaryOpInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getDef());
        op = ins.getOpcode();
        rhs = new WalaVarExpr(ins.getUse(0));
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
