package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class UnaryOpInstruction extends Instruction {

    public final VarExpr def;
    public final IUnaryOpInstruction.IOperator op;
    public final Expression rhs;

    public UnaryOpInstruction(SSAUnaryOpInstruction ins, VarExpr def, IUnaryOpInstruction.IOperator op, Expression rhs) {
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

    public SSAUnaryOpInstruction getOriginal() {
        return (SSAUnaryOpInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
