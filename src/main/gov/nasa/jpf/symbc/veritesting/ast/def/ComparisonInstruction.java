package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.ssa.SSAComparisonInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ComparisonInstruction extends Instruction {

    public final VarExpr def;
    public final Expression lhs;
    public final IComparisonInstruction.Operator op;
    public final Expression rhs;

    public ComparisonInstruction(SSAInstruction ins, VarExpr def, Expression lhs, IComparisonInstruction.Operator op, Expression rhs) {
        super(ins);
        this.def = def;
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
    }

    public ComparisonInstruction(SSAComparisonInstruction ins) {
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
