package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public class PutInstruction extends Instruction {

    public final VarExpr ref;
    public final FieldReference field;
    public final Expr assignExpr;

    public PutInstruction(SSAPutInstruction ins, VarExpr ref, FieldReference field, Expr assignExpr) {
        super(ins);
        this.ref = ref;
        this.field = field;
        this.assignExpr = assignExpr;
    }

    public PutInstruction(SSAPutInstruction ins) {
        super(ins);
        ref = new WalaVarExpr(ins.getRef());
        field = ins.getDeclaredField();
        assignExpr = new WalaVarExpr(ins.isStatic() ? ins.getUse(0) : ins.getUse(1));
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
