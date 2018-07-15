package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

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
