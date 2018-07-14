package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import com.ibm.wala.ssa.SSAInstruction;

public class WalaInstruction implements VeriExpression {
    private SSAInstruction instruction;

    public WalaInstruction(SSAInstruction ssaInstruction){
        this.instruction = ssaInstruction;
    }

    public SSAInstruction getInstruction() {
        return instruction;
    }

    public void setInstruction(SSAInstruction instruction) {
        this.instruction = instruction;
    }

    @Override
    public String toString() {
        return instruction.toString();
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitWalaInstruction(this);
    }
}
