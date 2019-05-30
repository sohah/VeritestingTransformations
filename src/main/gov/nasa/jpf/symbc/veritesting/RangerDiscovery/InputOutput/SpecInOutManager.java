package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

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
        discoverFreeInput();
        discoverStateVars();
        discoverOutputVar();
    }

    private void discoverFreeInput() {
        freeInput.add("sig", NamedType.INT);
    }

    private void discoverStateVars() {
        stateVars.add("start_bt", NamedType.BOOL);
        stateVars.add("launch_bt", NamedType.BOOL);
        stateVars.add("reset_bt", NamedType.BOOL);
    }

    private void discoverOutputVar() {
        inOutputVars.add("ignition", NamedType.BOOL);
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


    public List<String> getFreeInputs() {
        return freeInput.getInputNames();
    }

    public List<String> getInOutput() {
        return inOutputVars.getInputNames();
    }
}
