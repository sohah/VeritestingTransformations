package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import za.ac.sun.cs.green.expr.Expression;

public class CheckCastInstruction extends Instruction {

    public final Expression result;
    public final Expression val;
    public final TypeReference [] declaredResultTypes;

    public CheckCastInstruction(SSACheckCastInstruction ins, Expression result, Expression val, TypeReference [] declaredResultTypes) {
        super(ins);
        this.result = result;
        this.val = val;
        this.declaredResultTypes = declaredResultTypes;
    }

    public CheckCastInstruction(SSACheckCastInstruction ins) {
        super(ins);
        result = new WalaVarExpr(ins.getDef());
        val = new WalaVarExpr(ins.getUse(0));
        declaredResultTypes = ins.getDeclaredResultTypes();
    }

    public SSACheckCastInstruction getOriginal() {
        return (SSACheckCastInstruction)original;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
