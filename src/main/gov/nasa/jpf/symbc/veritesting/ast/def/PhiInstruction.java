package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAPhiInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class PhiInstruction extends Instruction {

    public final VarExpr def;
    public final Expression [] rhs;

    public PhiInstruction(SSAPhiInstruction ins, VarExpr def, Expression [] rhs) {
        super(ins);
        this.def = def;
        this.rhs = rhs;
    }

    public PhiInstruction(SSAPhiInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getDef());
        rhs = new Expression[ins.getNumberOfUses()];
        for (int i = 0; i < ins.getNumberOfUses(); i++) {
            rhs[i] = new WalaVarExpr(ins.getUse(i));
        }
    }

    public SSAPhiInstruction getOriginal() {
        return (SSAPhiInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
