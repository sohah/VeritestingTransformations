package gov.nasa.jpf.symbc.veritesting;

import gov.nasa.jpf.symbc.numeric.ComplexNonLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;

import java.util.HashMap;
import java.util.HashSet;


public class VeritestingRegion {

    public int getStartInsnPosition() {
        return startInsnPosition;
    }
    public void setStartInsnPosition(int startInsnPosition) {
        this.startInsnPosition = startInsnPosition;
    }
    private int startInsnPosition;

    public int getEndInsnPosition() {
        return endInsnPosition;
    }
    public void setEndInsnPosition(int endInsnPosition) {
        this.endInsnPosition = endInsnPosition;
    }
    private int endInsnPosition;

    public ComplexNonLinearIntegerExpression getCNLIE() {
        return cnlie;
    }
    public void setCNLIE(IntegerExpression CNLIE) {
        this.cnlie = (ComplexNonLinearIntegerExpression) CNLIE;
    }
    private ComplexNonLinearIntegerExpression cnlie;

    public HashSet<IntegerExpression> getOutputVars() {
        return outputVars;
    }
    public void setOutputVars(HashSet outputVars) {
        this.outputVars = outputVars;
    }
    private HashSet<IntegerExpression>  outputVars;

    public String getClassName() {
        return className;
    }

    public void setClassName(String className) {
        this.className = className;
    }

    public String getMethodName() {
        return methodName;
    }

    public void setMethodName(String methodName) {
        this.methodName = methodName;
    }

    private String className, methodName;

    public void setHoleHashMap(HashMap<IntegerExpression,IntegerExpression> holeHashMap) {
        this.holeHashMap = holeHashMap;
    }
    public HashMap<IntegerExpression, IntegerExpression> getHoleHashMap() {
        return holeHashMap;
    }
    private HashMap<IntegerExpression, IntegerExpression> holeHashMap;
}
