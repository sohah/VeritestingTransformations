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
        } else if (Config.spec.equals("wbs")) {
            discoverFreeInputWbs();
            discoverOutputVarWbs();
        } else if (Config.spec.equals("tcas")) {
            discoverFreeInputTcas();
            discoverOutputVarTcas();
        } else if (Config.spec.equals("vote")) {
            discoverFreeInputVote();
            discoverOutputVarVote();
        } else if (Config.spec.equals("vote2")) {
            discoverFreeInputVote2();
            discoverOutputVarVote2();
        } else {
            System.out.println("unexpected spec to run.!");
        }
    }
    //=========================== Pad ===========================

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


    //=========================== Even ===========================

    private void discoverOutputVarEven() {
        inOutputVars.add("out", NamedType.INT);
    }

    private void discoverFreeInputEven() {
        freeInput.add("signal", NamedType.BOOL);
    }

    private void discoverStateVarsEven() {
        stateVars.add("step", NamedType.INT);
    }


    //=========================== WBS ===========================

    private void discoverFreeInputWbs() {
        freeInput.add("pedal_r", NamedType.INT);
        freeInput.add("autoBreak_r", NamedType.BOOL);
        freeInput.add("skid_r", NamedType.BOOL);
    }


    private void discoverOutputVarWbs() {
        inOutputVars.add("NormalPressure_r", NamedType.INT);
        inOutputVars.add("AltPressure_r", NamedType.INT);
        inOutputVars.add("Sys_Mode", NamedType.INT);
    }

//=========================== TCAS ===========================

    private void discoverFreeInputTcas() {
        freeInput.add("Cur_Vertical_Sep_s", NamedType.INT);
        freeInput.add("High_Confidence_flag_s", NamedType.INT);
        freeInput.add("Two_of_Three_Reports_Valid_flag_s", NamedType.INT);
        freeInput.add("Own_Tracked_Alt_s", NamedType.INT);
        freeInput.add("Own_Tracked_Alt_Rate_s", NamedType.INT);
        freeInput.add("Other_Tracked_Alt_s", NamedType.INT);
        freeInput.add("Alt_Layer_Value_s", NamedType.INT);
        freeInput.add("Up_Separation_s", NamedType.INT);
        freeInput.add("Down_Separation_s", NamedType.INT);
        freeInput.add("Other_RAC_s", NamedType.INT);
        freeInput.add("Other_Capability_s", NamedType.INT);
        freeInput.add("Climb_Inhibit_s", NamedType.INT);
    }


    private void discoverOutputVarTcas() {
        inOutputVars.add("result_alt_sep_test_s", NamedType.INT);
        inOutputVars.add("alim_res_s", NamedType.INT);
    }


    //=========================== Vote ===========================
    private void discoverFreeInputVote() {
        freeInput.add("a", NamedType.BOOL);
        freeInput.add("b", NamedType.BOOL);
        freeInput.add("c", NamedType.BOOL);
        freeInput.add("threshold", NamedType.INT);
    }

    private void discoverOutputVarVote() {
        inOutputVars.add("out", NamedType.BOOL);
    }

    //=========================== Vote2 ===========================
    private void discoverFreeInputVote2() {
        freeInput.add("a", NamedType.INT);
        freeInput.add("b", NamedType.INT);
        freeInput.add("c", NamedType.INT);
        freeInput.add("threshold", NamedType.INT);
    }

    private void discoverOutputVarVote2() {
        inOutputVars.add("out", NamedType.BOOL);
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
