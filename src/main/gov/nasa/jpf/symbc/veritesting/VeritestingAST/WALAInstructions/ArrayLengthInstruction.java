package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSAArrayLengthInstruction;
import com.ibm.wala.ssa.SSAArrayLoadInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

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
