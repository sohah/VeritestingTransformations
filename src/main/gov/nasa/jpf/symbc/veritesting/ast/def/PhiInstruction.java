package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAPhiInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class PhiInstruction extends Instruction {

    public final VarExpr def;
    public final Expr [] rhs;

    public PhiInstruction(SSAPhiInstruction ins, VarExpr def, Expr [] rhs) {
        super(ins);
        this.def = def;
        this.rhs = rhs;
    }

    public PhiInstruction(SSAPhiInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getDef());
        rhs = new Expr [ins.getNumberOfUses()];
        for (int i = 0; i < ins.getNumberOfUses(); i++) {
            rhs[i] = new WalaVarExpr(ins.getUse(i));
        }
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
