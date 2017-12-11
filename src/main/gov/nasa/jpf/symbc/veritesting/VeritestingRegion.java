package gov.nasa.jpf.symbc.veritesting;

import gov.nasa.jpf.symbc.numeric.ComplexNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;

import java.util.HashMap;


public class VeritestingRegion {
    String[] localVars, intermediateVars, outputVars;
    ComplexNonLinearIntegerExpression cnlie;
    int endInsnPosition;
    HashMap<String, Integer> varStackSlots;


    public String[] getLocalVars() {
        return localVars;
    }

    public String[] getIntermediateVars() {
        return intermediateVars;
    }

    public ComplexNonLinearIntegerExpression getCNLIE() {
        return cnlie;
    }

    public int getEndInsnPosition() {
        return endInsnPosition;
    }

    public void setCNLIE(IntegerExpression CNLIE) {
        this.cnlie = (ComplexNonLinearIntegerExpression) CNLIE;
    }

    public String[] getOutputVars() {
        return outputVars;
    }

    public int getStackSlot(String var) {
        if(varStackSlots.containsKey(var)) return varStackSlots.get(var);
        else return -1;
    }
}
