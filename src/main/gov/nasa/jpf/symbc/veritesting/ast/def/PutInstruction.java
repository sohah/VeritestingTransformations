package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class PutInstruction extends Instruction {

    public final VarExpr def;
    public final FieldReference field;
    public final Expression assignExpr;

    public PutInstruction(SSAPutInstruction ins, VarExpr ref, FieldReference field, Expression assignExpr) {
        super(ins);
        this.def = ref;
        this.field = field;
        this.assignExpr = assignExpr;
    }

    public PutInstruction(SSAPutInstruction ins) {
        super(ins);
        def = new WalaVarExpr(ins.getRef());
        field = ins.getDeclaredField();
        assignExpr = new WalaVarExpr(ins.isStatic() ? ins.getUse(0) : ins.getUse(1));
    }

    public SSAPutInstruction getOriginal() {
        return (SSAPutInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
