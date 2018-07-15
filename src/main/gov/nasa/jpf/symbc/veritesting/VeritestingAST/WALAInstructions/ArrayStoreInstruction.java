package gov.nasa.jpf.symbc.veritesting.VeritestingAST.WALAInstructions;

import com.ibm.wala.ssa.SSAArrayLoadInstruction;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Expr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.AstVisitor;

public class ArrayStoreInstruction extends Instruction {

    public final VarExpr arrayref;
    public final VarExpr index;
    public final TypeReference elementType;
    public final Expr assignExpr;

    public ArrayStoreInstruction(SSAInstruction ins, VarExpr arrayref, VarExpr index, TypeReference elementType, Expr assigned) {
        super(ins);
        this.arrayref = arrayref;
        this.index = index;
        this.elementType = elementType;
        this.assignExpr = assigned;
    }

    public ArrayStoreInstruction(SSAArrayStoreInstruction ins) {
        super(ins);
        arrayref = new WalaVarExpr(ins.getArrayRef());
        index = new WalaVarExpr(ins.getIndex());
        elementType = ins.getElementType();
        assignExpr = new WalaVarExpr(ins.getDef());
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(this);
    }
}
