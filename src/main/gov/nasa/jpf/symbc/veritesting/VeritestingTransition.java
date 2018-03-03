package gov.nasa.jpf.symbc.veritesting;

import za.ac.sun.cs.green.expr.Expression;

public class VeritestingTransition {
    public int pathLabel;
    public String pathLabelString;
    public Expression transitionConstraint;
    public String instructionName;


    public VeritestingTransition(Expression transitionConstraint, String instructionName, String pathLabelString, int pathLabel){
        this.pathLabelString = pathLabelString;
        this.pathLabel = pathLabel;
        this.transitionConstraint = transitionConstraint;
        this.instructionName = instructionName;
    }

    public String getInstructionName() {
        return instructionName;
    }

    public Expression getTransitionConstraint() {
        return transitionConstraint;
    }

    public int getPathLabel() {
        return pathLabel;
    }

    public String getPathLabelString() {
        return pathLabelString;
    }

    public void setTransitionConstraint(Expression transitionConstraint) {
        this.transitionConstraint = transitionConstraint;
    }

    public void setPathLabel(int exceptionPathLabel) {
        this.pathLabel = exceptionPathLabel;
    }

    public void setInstructionName(String instructionName) {
        this.instructionName = instructionName;
    }

    public void setPathLabelString(String pathLabelString) {
        this.pathLabelString = pathLabelString;
    }

    @Override
    public String toString() {
        return("instruction = " + instructionName + ", "+ pathLabelString + " = " + pathLabel +", transitionConstraint = " + transitionConstraint.toString() );
    }
}
