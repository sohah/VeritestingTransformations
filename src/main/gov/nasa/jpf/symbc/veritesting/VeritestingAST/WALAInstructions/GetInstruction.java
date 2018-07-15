package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public class GetInstruction extends Instruction {

    public final VarExpr ref;
    public final FieldReference field;
    public final VarExpr def;

    public GetInstruction(SSAGetInstruction ins, VarExpr ref, FieldReference field, VarExpr def) {
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
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
