package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAArrayLengthInstruction;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class ArrayLengthInstruction extends Instruction {

    public final Expression arrayref;
    public final Expression def;

    public ArrayLengthInstruction(SSAArrayLengthInstruction ins, Expression arrayref, Expression def) {
        super(ins);
        this.arrayref = arrayref;
        this.def = def;
    }

    public SSAArrayLengthInstruction getOriginal() {
        return (SSAArrayLengthInstruction)original;
    }

    public ArrayLengthInstruction(SSAArrayLengthInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        def = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n"+ def + " = arrayLength (" +arrayref +")";
    }
}
