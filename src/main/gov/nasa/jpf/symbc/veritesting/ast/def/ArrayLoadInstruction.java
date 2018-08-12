package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAArrayLoadInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is ArrayLoadInstruction in RangerIR that matches the corresponding ArrayLoadInstruction in Wala and subsequently the instruction in Java Bytecode.
 */
public class ArrayLoadInstruction extends Instruction {

    public final Expression arrayref;
    public final Expression index;
    public final TypeReference elementType;
    public final Expression def;

    public ArrayLoadInstruction(SSAArrayLoadInstruction ins, Expression arrayref, Expression index,
                                TypeReference elementType, Expression def) {
        super(ins);
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
        this.def = def;
    }

    public SSAArrayLoadInstruction getOriginal() {
        return (SSAArrayLoadInstruction)original;
    }

    public ArrayLoadInstruction(SSAArrayLoadInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        index = new WalaVarExpr(ins.getIndex());
        elementType = ins.getElementType();
        def = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n" + def + " = "+ arrayref + "[" + index+":"+elementType +"]";
    }
}
