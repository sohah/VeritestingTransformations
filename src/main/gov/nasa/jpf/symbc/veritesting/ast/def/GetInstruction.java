package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class GetInstruction extends Instruction {

    public final VarExpr ref;
    public final FieldReference field;
    public final VarExpr def;

    public GetInstruction(SSAInstruction ins, VarExpr def, VarExpr ref, FieldReference field) {
        super(ins);
        this.ref = ref;
        this.field = field;
        this.def = def;
    }

    public GetInstruction(SSAGetInstruction ins) {
        super(ins);
        ref = new WalaVarExpr(ins.getRef());
        field = ins.getDeclaredField();
        def = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
