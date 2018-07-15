package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.shrikeBT.IComparisonInstruction;
import com.ibm.wala.ssa.SSAComparisonInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class ComparisonInstruction extends Instruction {

    public final VarExpr def;
    public final Expr lhs;
    public final IComparisonInstruction.Operator op;
    public final Expr rhs;

    public ComparisonInstruction(SSAInstruction ins, VarExpr def, Expr lhs, IComparisonInstruction.Operator op, Expr rhs) {
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
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
