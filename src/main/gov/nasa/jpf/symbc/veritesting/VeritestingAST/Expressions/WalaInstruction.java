package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeritestingExpression;

public class WalaInstruction implements VeritestingExpression {
    private SSAInstruction instruction;


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
}
