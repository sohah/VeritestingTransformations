package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAArrayLoadInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;

public class ArrayLoadInstruction extends Instruction {

    public final VarExpr arrayref;
    public final VarExpr index;
    public final TypeReference elementType;
    public final VarExpr def;

    public ArrayLoadInstruction(SSAInstruction ins, VarExpr arrayref, VarExpr index, TypeReference elementType, VarExpr def) {
        super(ins);
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
        this.def = def;
    }

    public ArrayLoadInstruction(SSAArrayLoadInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        index = new WalaVarExpr(ins.getIndex());
        elementType = ins.getElementType();
        def = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
