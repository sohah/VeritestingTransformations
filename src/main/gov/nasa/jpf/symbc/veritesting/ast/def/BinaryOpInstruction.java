package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class BinaryOpInstruction extends Instruction {

    public final VarExpr def;
    public final Expression lhs;
    public final IBinaryOpInstruction.IOperator op;
    public final Expression rhs;

    public BinaryOpInstruction(SSAInstruction ins, VarExpr def, Expression lhs, IBinaryOpInstruction.IOperator op, Expression rhs) {
        super(ins);
        this.def = def;
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }

    public BinaryOpInstruction(SSABinaryOpInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getDef());
        lhs = new WalaVarExpr(ins.getUse(0));
        op = ins.getOperator();
        rhs = new WalaVarExpr(ins.getUse(1));
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
