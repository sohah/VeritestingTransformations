package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import jkind.lustre.NamedType;

import java.util.List;


/**
 * this class manages the input and output of TNODE, RNODE uses another class that inherets from this one and adds a few extra functions.
 */
public class SpecInOutManager {

    SpecInputOutput freeInput = new SpecInputOutput();
    SpecInputOutput stateVars = new SpecInputOutput();

    // holds the inputs in the contract which are the outputs, i.e., which constrain the output.
    SpecInputOutput inOutputVars = new SpecInputOutput();

    public void discoverVars() {
        if (Config.spec.equals("pad")) {
            discoverFreeInputPad();
            discoverStateVarsPad();
            discoverOutputVarPad();
        } else if (Config.spec.equals("even")) {
            discoverFreeInputEven();
            discoverStateVarsEven();
            discoverOutputVarEven();
        } else {
            System.out.println("unexpected spec to run.!");
        }
    }

    private void discoverFreeInputPad() {
        freeInput.add("sig", NamedType.INT);
    }

    private void discoverStateVarsPad() {
        stateVars.add("start_bt", NamedType.BOOL);
        stateVars.add("launch_bt", NamedType.BOOL);
        stateVars.add("reset_bt", NamedType.BOOL);
    }

    private void discoverOutputVarPad() {
        inOutputVars.add("ignition", NamedType.BOOL);
    }


    private void discoverOutputVarEven() {
        inOutputVars.add("out", NamedType.INT);
    }

    private void discoverFreeInputEven() {
        freeInput.add("signal", NamedType.BOOL);
    }

    private void discoverStateVarsEven() {
        stateVars.add("step", NamedType.INT);
    }


    /**
     * searches in all in input and output arrays to check if it is one in them
     *
     * @param s
     * @return
     */
    public boolean isInOutVar(String s, NamedType type) {
        return isFreeInVar(s, type) || isStateInVar(s, type) || isStateOutVar(s, type);
    }


    public boolean isFreeInVar(String varName, NamedType type) {
        return freeInput.contains(varName, type);
    }

    public boolean isStateInVar(String varName, NamedType type) {
        return stateVars.contains(varName, type);
    }

    public boolean isStateOutVar(String varName, NamedType type) {
        return inOutputVars.contains(varName, type);
    }


    public SpecInputOutput getFreeInputs() {
        return freeInput;
    }

    public List<String> getFreeInputNames() {
        return freeInput.getInputNames();
    }

    public SpecInputOutput getInOutput() {
        return inOutputVars;
    }
}
