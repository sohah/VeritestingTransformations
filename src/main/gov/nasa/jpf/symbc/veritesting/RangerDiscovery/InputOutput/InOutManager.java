package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;


/**
 * this class manages the input and output of RNode, it assumes that the input and the output of the "step" function is
 * provided, it is divided into 4 types, freeInput, stateInput, stateOutput and contractOutput. The type of those
 * should match the signature of the step function. Type conversion is needed sometimes, if so then the variable
 * names in the arraylist will change to the new var being created, in this case there will be as well a side effect
 * for the equations needed for conversion between the original var and the new var being created for conversion.
 * <p>
 * An important thing to note here is that the signature of the different input, output, or state are reflecting those
 * in the implementation type.
 */

/**
 * State output refers to any state variable that the class keeps track of in each iteration, it really depends on
 * the implementation.
 * Contract output on the other hand refers to outputs that the specification are going to use to check specific
 * constraints. With this definition, contract output has nothing to do with the actual output of the contract in the
 * implementation, for the specification can be checking really multiple things.
 * <p>
 * There is an overlap between state output and contract output, when plugging in things we need to be careful about
 * what each term means. i.e., for those state variables that are going to be checked with the specification, even
 * though they are part of the state and therefore might be considered as state output, they are however checked by
 * the sepecification and with this regard they are defined as contract output instead. They should not be included as
 * a state output, only as a contract output.
 */
public class InOutManager {

    //for now we are adding the reference object by hand, it changes from lunix to mac, so I am adding this here to avoid having to repeatedly change the code
    //private String referenceObjectName = "r351"; //for lunix

    private String referenceObjectName = "r347"; //for mac

    //this number is very important it should be the same between the passed inputs into the spec that we think is an
    // output of the model and it must also be the same size as the list in contractOutput
    public static int wrapperOutputNum;

    Input freeInput = new Input();
    Input stateInput = new Input();

    //This is the state output of the class in the implementation.
    ContractOutput stateOutput = new ContractOutput();

    //This describes the output that is going to be validated with the specification, they are usually part of the
    // state but should NOT be mistaken as a stateOutput, a stateOutput are only those needed internally for R node
    // and are not validated by the spec, for those that needs to be  validated by the sepc we call the
    // contractOutput and must be populated there.
    ContractOutput contractOutput = new ContractOutput();

    boolean isOutputConverted = false;

    //carries any type conversion equation which can be triggered both in case of the input and the output
    ArrayList<Equation> typeConversionEq = new ArrayList<>();

    ArrayList<VarDecl> conversionLocalList = new ArrayList<>();

    public ArrayList<Equation> getTypeConversionEq() {
        return typeConversionEq;
    }

    public ArrayList<VarDecl> getConversionLocalList() {
        return conversionLocalList;
    }

    public boolean isOutputConverted() {
        return isOutputConverted;
    }

    public void discoverVars() {
        if (Config.spec.equals("pad")) {
            discoverFreeInputPad();
            doFreeTypeConversion();

            discoverStateInputPad();
            doStateInputTypeConversion();

            discoverStateOutputPad();
            doStateOutputTypeConversion();

            discoverContractOutputPad();
            doContractOutputTypeConversion();

        } else if (Config.spec.equals("even")) {
            discoverFreeInputEven();
            doFreeTypeConversion();

            discoverStateInputEven();
            doStateInputTypeConversion();

            discoverStateOutputEven();
            doStateOutputTypeConversion();

            discoverContractOutputEven();
            doContractOutputTypeConversion();

        } else if (Config.spec.equals("wbs")) {
            discoverFreeInputWBS();
            doFreeTypeConversion();

            discoverStateInputWBS();
            doStateInputTypeConversion();

            discoverStateOutputWBS();
            doStateOutputTypeConversion();

            discoverContractOutputWBS();
            doContractOutputTypeConversion();
        } else if (Config.spec.equals("tcas")) {
            discoverFreeInputTCAS();
            doFreeTypeConversion();

            discoverStateInputTCAS();
            doStateInputTypeConversion();

            discoverStateOutputTCAS();
            doStateOutputTypeConversion();

            discoverContractOutputTCAS();
            doContractOutputTypeConversion();

        } else if (Config.spec.equals("vote")) {
            discoverFreeInputVote();
            doFreeTypeConversion();

            discoverStateInputVote();
            doStateInputTypeConversion();

            discoverStateOutputVote();
            doStateOutputTypeConversion();

            discoverContractOutputVote();
            doContractOutputTypeConversion();

        } else if (Config.spec.equals("vote2")) {
            discoverFreeInputVote2();
            doFreeTypeConversion();

            discoverStateInputVote2();
            doStateInputTypeConversion();

            discoverStateOutputVote2();
            doStateOutputTypeConversion();

            discoverContractOutputVote2();
            doContractOutputTypeConversion();

        } else {
            System.out.println("unexpected spec to run.!");
            assert false;
        }
        wrapperOutputNum = contractOutput.size;

        checkAsserts();
    }

    private void checkAsserts() {
        assert contractOutput.varInitValuePair.size() == contractOutput.varList.size();
        assert stateOutput.varInitValuePair.size() == stateOutput.varList.size();
        assert freeInput.size > 0;
        assert wrapperOutputNum == contractOutput.size;

    }

    //================================= Type Conversion ========================

    private void doContractOutputTypeConversion() {
        if (contractOutput.containsBool()) { // isn't that replicated with the state output.
            ArrayList<Equation> conversionResult = contractOutput.convertOutput();
            assert conversionResult.size() == 1;
            typeConversionEq.addAll(conversionResult);
            isOutputConverted = true;
        }
    }

    private void doFreeTypeConversion() {
        if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }
    }

    private void doStateInputTypeConversion() {
        if (stateInput.containsBool()) { //type conversion to spf int type is needed
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = stateInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }
    }

    private void doStateOutputTypeConversion() {
        if (stateOutput.containsBool()) {
            ArrayList<Equation> conversionResult = stateOutput.convertOutput();
            typeConversionEq.addAll(conversionResult);
            //conversionLocalList.addAll(conversionResult.getFirst()); // no need to add this, since these are already as
            // def in the dynStmt
            isOutputConverted = true;
        }
    }

    //================================= end Type Conversion ========================


    //================================= Pad ========================
    //entered by hand for now -- this is a singleton, I need to enforce this everywhere.
    private void discoverContractOutputPad() {
        contractOutput.add(referenceObjectName + ".ignition_r.1.7.4", NamedType.BOOL);
        contractOutput.addInit(referenceObjectName + ".ignition_r.1.7.4", new BoolExpr(false));
    }


    //entered by hand for now
    private void discoverFreeInputPad() {
        freeInput.add("signal", NamedType.INT);
    }


    //entered by hand for now
    private void discoverStateInputPad() {
        stateInput.add("start_btn", NamedType.BOOL);
        stateInput.add("launch_btn", NamedType.BOOL);
        stateInput.add("reset_btn", NamedType.BOOL);
        stateInput.add("ignition", NamedType.BOOL);

    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputPad() {
        stateOutput.add(referenceObjectName + ".start_btn.1.15.4", NamedType.BOOL);
        stateOutput.addInit(referenceObjectName + ".start_btn.1.15.4", new BoolExpr(false));

        stateOutput.add(referenceObjectName + ".launch_btn.1.17.4", NamedType.BOOL);
        stateOutput.addInit(referenceObjectName + ".start_btn.1.15.4", new BoolExpr(false));

        stateOutput.add(referenceObjectName + ".reset_btn.1.9.4", NamedType.BOOL);
        stateOutput.addInit(referenceObjectName + ".start_btn.1.15.4", new BoolExpr(false));

    }


    //====================== WBS ====================================

    //entered by hand for now - this defines the output that we expect to validate with the T_node,i.e, this is the
    // output of the wrapper that gets plugged in the T_node to  validate it. Therefore it is not directly reflecting
    // the method output of the implementation, instead it is the output of the to-be-created r_wrapper node.

    private void discoverContractOutputWBS() {

        contractOutput.add(referenceObjectName + ".Nor_Pressure.1.13.2", NamedType.INT);
        contractOutput.addInit(referenceObjectName + ".Nor_Pressure.1.13.2", new IntExpr(0));

        contractOutput.add(referenceObjectName + ".Alt_Pressure.1.13.2", NamedType.INT);
        contractOutput.addInit(referenceObjectName + ".Alt_Pressure.1.13.2", new IntExpr(0));

        contractOutput.add(referenceObjectName + ".Sys_Mode.1.5.2", NamedType.INT);
        contractOutput.addInit(referenceObjectName + ".Sys_Mode.1.5.2", new IntExpr(0));

    }

    //entered by hand for now
    private void discoverFreeInputWBS() {
        freeInput.add("pedal", NamedType.INT);
        freeInput.add("autoBrake", NamedType.BOOL);
        freeInput.add("skid", NamedType.BOOL);

        /*if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now
    private void discoverStateInputWBS() {
        stateInput.add("WBS_Node_WBS_BSCU_SystemModeSelCmd_rlt_PRE", NamedType.INT);
        stateInput.add("WBS_Node_WBS_BSCU_rlt_PRE1", NamedType.INT);
        stateInput.add("WBS_Node_WBS_rlt_PRE2", NamedType.INT);

        stateInput.add("Nor_Pressure", NamedType.INT);
        stateInput.add("Alt_Pressure", NamedType.INT);
        stateInput.add("Sys_Mode", NamedType.INT);

    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputWBS() {

        stateOutput.add(referenceObjectName + ".WBS_Node_WBS_BSCU_SystemModeSelCmd_rlt_PRE.1.3.2", NamedType.INT);
        stateOutput.addInit(referenceObjectName + ".WBS_Node_WBS_BSCU_SystemModeSelCmd_rlt_PRE.1.3.2", new IntExpr(0));


        stateOutput.add(referenceObjectName + ".WBS_Node_WBS_BSCU_rlt_PRE1.1.3.2", NamedType.INT);
        stateOutput.addInit(referenceObjectName + ".WBS_Node_WBS_BSCU_rlt_PRE1.1.3.2", new IntExpr(0));


        stateOutput.add(referenceObjectName + ".WBS_Node_WBS_rlt_PRE2.1.3.2", NamedType.INT);
        stateOutput.addInit(referenceObjectName + ".WBS_Node_WBS_rlt_PRE2.1.3.2", new IntExpr(0));

    }



    //====================== TCAS ====================================

    //entered by hand for now - this defines the output that we expect to validate with the T_node,i.e, this is the
    // output of the wrapper that gets plugged in the T_node to  validate it. Therefore it is not directly reflecting
    // the method output of the implementation, instead it is the output of the to-be-created r_wrapper node.

    private void discoverContractOutputTCAS() {

        contractOutput.add("r-1.result_alt_sep_test.1.4.33", NamedType.INT);
        contractOutput.addInit("r-1.result_alt_sep_test.1.4.33", new IntExpr(0));

        contractOutput.add("r-1.alim_res.1.4.33", NamedType.INT);
        contractOutput.addInit("r-1.alim_res.1.4.33", new IntExpr(0));
    }


    //entered by hand for now
    private void discoverFreeInputTCAS() {
        freeInput.add("Cur_Vertical_Sep", NamedType.INT);
        freeInput.add("High_Confidence_flag", NamedType.INT);
        freeInput.add("Two_of_Three_Reports_Valid_flag", NamedType.INT);
        freeInput.add("Own_Tracked_Alt", NamedType.INT);
        freeInput.add("Own_Tracked_Alt_Rate", NamedType.INT);
        freeInput.add("Other_Tracked_Alt", NamedType.INT);
        freeInput.add("Alt_Layer_Value", NamedType.INT);
        freeInput.add("Up_Separation", NamedType.INT);
        freeInput.add("Down_Separation", NamedType.INT);
        freeInput.add("Other_RAC", NamedType.INT);
        freeInput.add("Other_Capability", NamedType.INT);
        freeInput.add("Climb_Inhibit", NamedType.INT);

        /*if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now
    private void discoverStateInputTCAS() {
/*
// constants -- not an input.
        stateInput.add("OLEV", NamedType.INT);
        stateInput.add("MAXALTDIFF", NamedType.INT);
        stateInput.add("MINSEP", NamedType.INT);
        stateInput.add("NOZCROSS", NamedType.INT);
        stateInput.add("NO_INTENT", NamedType.INT);
        stateInput.add("DO_NOT_CLIMB", NamedType.INT);
        stateInput.add("DO_NOT_DESCEND", NamedType.INT);
        stateInput.add("TCAS_TA", NamedType.INT);
        stateInput.add("OTHER", NamedType.INT);
*/

        stateInput.add("High_Confidence", NamedType.INT);
        stateInput.add("Two_of_Three_Reports_Valid", NamedType.INT);
        stateInput.add("Positive_RA_Alt_Thresh_0", NamedType.INT);
        stateInput.add("Positive_RA_Alt_Thresh_1", NamedType.INT);
        stateInput.add("Positive_RA_Alt_Thresh_2", NamedType.INT);
        stateInput.add("Positive_RA_Alt_Thresh_3", NamedType.INT);

        stateInput.add("result_alt_sep_test", NamedType.INT);
        stateInput.add("alim_res", NamedType.INT);
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputTCAS() {

        //commenting these out even though they capture a side-effect and thus can be thought of as state output,
        // they are in fact the input in TCAS, thus we need not capture them.

        /*contractOutput.add("r-1.Cur_Vertical_Sep.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Cur_Vertical_Sep.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Own_Tracked_Alt.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Own_Tracked_Alt.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Own_Tracked_Alt_Rate.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Own_Tracked_Alt_Rate.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Other_Tracked_Alt.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Other_Tracked_Alt.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Alt_Layer_Value.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Alt_Layer_Value.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Up_Separation.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Up_Separation.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Down_Separation.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Down_Separation.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Other_RAC.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Other_RAC.1.3.32", new IntExpr(0));

        contractOutput.add("r-1.Other_Capability.1.3.32", NamedType.INT);
        contractOutput.addInit("r-1.Other_Capability.1.3.32", new IntExpr(0));
*/
        stateOutput.add("r-1.High_Confidence.1.5.33", NamedType.INT);
        stateOutput.addInit("r-1.High_Confidence.1.5.33", new IntExpr(0));

        stateOutput.add("r-1.Two_of_Three_Reports_Valid.1.5.33", NamedType.INT);
        stateOutput.addInit("r-1.Two_of_Three_Reports_Valid.1.5.33", new IntExpr(0));

        stateOutput.add("r-1.Positive_RA_Alt_Thresh_0.1.3.33", NamedType.INT);
        stateOutput.addInit("r-1.Positive_RA_Alt_Thresh_0.1.3.33", new IntExpr(0));

        stateOutput.add("r-1.Positive_RA_Alt_Thresh_1.1.3.33", NamedType.INT);
        stateOutput.addInit("r-1.Positive_RA_Alt_Thresh_1.1.3.33", new IntExpr(0));

        stateOutput.add("r-1.Positive_RA_Alt_Thresh_2.1.3.33", NamedType.INT);
        stateOutput.addInit("r-1.Positive_RA_Alt_Thresh_2.1.3.33", new IntExpr(0));

        stateOutput.add("r-1.Positive_RA_Alt_Thresh_3.1.3.33", NamedType.INT);
        stateOutput.addInit("r-1.Positive_RA_Alt_Thresh_3.1.3.33", new IntExpr(0));
    }


    //=========================== Even ============================
    //entered by hand for now

    private void discoverContractOutputEven() {
        contractOutput.add(referenceObjectName + ".output.1.5.2", NamedType.INT);
        contractOutput.addInit(referenceObjectName + ".output.1.5.2", new IntExpr(8));
    }

    //entered by hand for now
    private void discoverFreeInputEven() {
        freeInput.add("signal", NamedType.BOOL);
        /*if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now
    private void discoverStateInputEven() {
        stateInput.add("countState", NamedType.INT);
        stateInput.add("output", NamedType.INT);
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputEven() {
        stateOutput.add(referenceObjectName + ".countState.1.5.2", NamedType.INT);
        stateOutput.addInit(referenceObjectName + ".countState.1.5.2", new IntExpr(0));

    }


    //=========================== Vote ===========================

    private void discoverContractOutputVote() {

        contractOutput.add(referenceObjectName + ".out.1.3.2", NamedType.BOOL);
        contractOutput.addInit(referenceObjectName + ".out.1.3.2", new BoolExpr(false));
        /*if (contractOutput.containsBool()) { // isn't that replicated with the state output.
            ArrayList<Equation> conversionResult = contractOutput.convertOutput();
            assert conversionResult.size() == 1;
            typeConversionEq.addAll(conversionResult);
            isOutputConverted = true;
        }*/
    }

    //entered by hand for now
    private void discoverFreeInputVote() {
        freeInput.add("a", NamedType.BOOL);
        freeInput.add("b", NamedType.BOOL);
        freeInput.add("c", NamedType.BOOL);
        freeInput.add("threshold", NamedType.INT);

        /*if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now
    private void discoverStateInputVote() {
        stateInput.add("out", NamedType.BOOL);
        /*if (stateInput.containsBool()) { //type conversion to spf int type is needed
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = stateInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputVote() {
    }


    //=========================== Vote2 ===========================

    private void discoverContractOutputVote2() {

        contractOutput.add(referenceObjectName + ".out.1.18.2", NamedType.BOOL);
        contractOutput.addInit(referenceObjectName + ".out.1.18.2", new BoolExpr(false));
        /*if (contractOutput.containsBool()) { // isn't that replicated with the state output.
            ArrayList<Equation> conversionResult = contractOutput.convertOutput();
            assert conversionResult.size() == 1;
            typeConversionEq.addAll(conversionResult);
            isOutputConverted = true;
        }*/
    }

    //entered by hand for now
    private void discoverFreeInputVote2() {
        freeInput.add("a", NamedType.INT);
        freeInput.add("b", NamedType.INT);
        freeInput.add("c", NamedType.INT);
        freeInput.add("threshold", NamedType.INT);

        /*if (freeInput.containsBool()) {
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = freeInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now
    private void discoverStateInputVote2() {
        stateInput.add("out", NamedType.BOOL);
        /*if (stateInput.containsBool()) { //type conversion to spf int type is needed
            Pair<ArrayList<VarDecl>, ArrayList<Equation>> conversionResult = stateInput.convertInput();
            typeConversionEq.addAll(conversionResult.getSecond());
            conversionLocalList.addAll(conversionResult.getFirst());
        }*/
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutputVote2() {
    }


    public ArrayList<VarDecl> generateInputDecl() {
        ArrayList<VarDecl> inputDeclList = generateFreeInputDecl();
        inputDeclList.addAll(generateStateInputDecl());
        return inputDeclList;
    }

    public ArrayList<VarDecl> generateFreeInputDecl() {
        return generateLustreDecl(freeInput);
    }

    public ArrayList<VarDecl> generateStateInputDecl() {
        return generateLustreDecl(stateInput);
    }

    private ArrayList<VarDecl> generateLustreDecl(SpecInputOutput inputOutput) {
        return inputOutput.generateVarDecl();
    }

    public ArrayList<VarDecl> generaterContractOutDeclList() {
        return contractOutput.generateVarDecl();
    }

    public ArrayList<VarDecl> generateOutputDecl() {
        return stateOutput.generateVarDecl();
    }

    /**
     * searches in all in input and output arrays to check if it is one in them
     *
     * @param s
     * @return
     */
    public boolean isInOutVar(String s, NamedType type) {
        return isFreeInVar(s, type) || isStateInVar(s, type) || isStateOutVar(s, type) || isContractOutputVar(s, type);
    }


    public boolean isFreeInVar(String varName, NamedType type) {
        return freeInput.contains(varName, type);
    }

    public boolean isStateInVar(String varName, NamedType type) {
        return stateInput.contains(varName, type);
    }

    public boolean isStateOutVar(String varName, NamedType type) {
        return stateOutput.contains(varName, type);
    }

    public boolean isContractOutputVar(String varName, NamedType type) {
        return contractOutput.contains(varName, type);
    }

    public boolean isContractOutputStr(String name) {
        return contractOutput.hasName(name);
    }

    public boolean isStateOutVar(String name) {
        return stateOutput.hasName(name);
    }

    public Pair<VarDecl, Equation> replicateContractOutput(String outVarName) {
        return contractOutput.replicateMe(outVarName);
    }

    public NamedType getContractOutType() {
        if (contractOutput.varList.size() == 0) {
            System.out.println("Contract has no output, this is unexpected signature for contract R! Aborting!");
            assert false;
        }
        return contractOutput.varList.get(0).getSecond();
    }

    //gets the initial value of a wrapper output.
    public Expr getContractOutputInit(String name) {
        return contractOutput.getReturnInitVal(name);
    }

    public Expr getStateOutInit(String name) {
        return stateOutput.getReturnInitVal(name);
    }

    public int getContractOutputCount() {
        return contractOutput.size;
    }
}
