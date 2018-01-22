package gov.nasa.jpf.symbc.veritesting;


import za.ac.sun.cs.green.expr.Expression;

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

    public Expression getSummaryExpression() {
        return summaryExpression;
    }
    public void setSummaryExpression(Expression CNLIE) {
        this.summaryExpression = CNLIE;
    }
    private Expression summaryExpression;

    public HashSet<Expression> getOutputVars() {
        return outputVars;
    }
    public void setOutputVars(HashSet outputVars) {
        this.outputVars = outputVars;
    }
    private HashSet<Expression>  outputVars;

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

    public void setHoleHashMap(HashMap<Expression,Expression> holeHashMap) {
        this.holeHashMap = holeHashMap;
    }
    public HashMap<Expression, Expression> getHoleHashMap() {
        return holeHashMap;
    }
    private HashMap<Expression, Expression> holeHashMap;

    public void setIsMethodSummary(boolean isMethodSummary) {
        this.isMethodSummary = isMethodSummary;
    }
    public boolean isMethodSummary() {
        return isMethodSummary;
    }
    private boolean isMethodSummary = false;

    public void setRetValVars(Expression retVal) {
        this.retVal = retVal;
    }
    public Expression retVal;

    public String toString() {
        return "(" + className + ", " + methodName + ", " + startInsnPosition + ", " + endInsnPosition +
                ", BB" + startBBNum + ", BB" + endBBNum + ", " + getNumBranchesSummarized() + ")";
    }

    public void setMethodSignature(String methodSignature) {
        this.methodSignature = methodSignature;
    }
    public String getMethodSignature() {
        return methodSignature;
    }
    String methodSignature;

    public void setSummarizedRegionStartBB(HashSet<Integer> summarizedRegionStartBB) {
        this.summarizedRegionStartBB = new HashSet<>();
        this.summarizedRegionStartBB.addAll(summarizedRegionStartBB);
    }
    public HashSet<Integer> summarizedRegionStartBB = null;

    public int ranIntoCount = 0, usedCount = 0;

    public int getNumBranchesSummarized() {
        return summarizedRegionStartBB.size();
    }

    public void setEndBBNum(int endBBNum) {
        this.endBBNum = endBBNum;
    }
    public int endBBNum;

    public void setStartBBNum(int startBBNum) {
        this.startBBNum = startBBNum;
    }
    public int startBBNum;
}

