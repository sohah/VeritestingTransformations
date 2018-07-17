package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ArrayStoreInstruction extends Instruction {

    public final VarExpr arrayref;
    public final VarExpr index;
    public final TypeReference elementType;
    public final Expression assignExpr;

    public ArrayStoreInstruction(SSAArrayStoreInstruction ins, VarExpr arrayref, VarExpr index, TypeReference elementType, Expression assigned) {
        super(ins);
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
        this.assignExpr = assigned;
    }

    public SSAArrayStoreInstruction getOriginal() {
        return (SSAArrayStoreInstruction)original;
    }

    public ArrayStoreInstruction(SSAArrayStoreInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        index = new WalaVarExpr(ins.getIndex());
        elementType = ins.getElementType();
        assignExpr = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
