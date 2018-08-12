package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.FieldReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

/**
 * This is GetInstruction in Ranger IR that matches the corresponding GetInstruction in Wala and subsequently the instruction in Java Bytecode.
 */
public class GetInstruction extends Instruction {

    public final Expression ref;
    public final FieldReference field;
    public final Expression def;

    public GetInstruction(SSAGetInstruction ins, Expression def, Expression ref, FieldReference field) {
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

    public SSAGetInstruction getOriginal() {
        return (SSAGetInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "\n"+ def + " = get("+ ref + "."+field + ")";
    }
}
