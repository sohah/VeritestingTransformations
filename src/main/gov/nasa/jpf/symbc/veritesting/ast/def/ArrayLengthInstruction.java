package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAArrayLengthInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class ArrayLengthInstruction extends Instruction {

    public final VarExpr arrayref;
    public final VarExpr def;

    public ArrayLengthInstruction(SSAArrayLengthInstruction ins, VarExpr arrayref, VarExpr def) {
        super(ins);
        this.arrayref = arrayref;
        this.def = def;
    }

    public ArrayLengthInstruction(SSAArrayLengthInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        def = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
