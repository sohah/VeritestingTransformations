package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import jkind.lustre.*;

import java.util.ArrayList;


/**
 * this class manages the input and output of RNode, it assumes that the input and the output of the "step" function is
 * provided, it is divided into 4 types, freeInput, stateInput, stateOutput and methodOutput. The type of those
 * should match the signature of the step function. Type conversion is needed sometimes, if so then the variable
 * names in the arraylist will change to the new var being created, in this case there will be as well a side effect
 * for the equations needed for conversion between the original var and the new var being created for conversion.
 */
public class InOutManager {

    InputOutput freeInput = new InputOutput();
    InputOutput stateInput = new InputOutput();
    InputOutput stateOutput = new InputOutput();
    InputOutput methodOutput = new InputOutput();

    ArrayList<Equation> typeConversionEq = new ArrayList<>();

    public ArrayList<Equation> getTypeConversionEq() {
        return typeConversionEq;
    }

    public void discoverVars(){
        discoverFreeInput();
        discoverStateInput();
        discoverStateOutput();
        discoverMethodOutput();
    }

    //entered by hand for now
    private void discoverMethodOutput() {
        methodOutput.add("r347.ignition_r.1.7.4", NamedType.BOOL);
        typeConversionEq.addAll(methodOutput.convertOutput());
    }

    //entered by hand for now
    private void discoverFreeInput(){
        freeInput.add("signal", NamedType.INT);
    }

    //entered by hand for now
    private void discoverStateInput(){
        stateInput.add("start_btn", NamedType.BOOL);
        stateInput.add("launch_btn", NamedType.BOOL);
        stateInput.add("ignition", NamedType.BOOL);
        stateInput.add("reset_btn", NamedType.BOOL);
        typeConversionEq.addAll(stateInput.convertInput());
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutput(){
        stateOutput.add("r347.start_btn.1.15.4", NamedType.BOOL);
        stateOutput.add("r347.launch_btn.1.17.4", NamedType.BOOL);
        stateOutput.add("r347.reset_btn.1.9.4", NamedType.BOOL);
        typeConversionEq.addAll(stateOutput.convertOutput());
    }

    public ArrayList<VarDecl> generateInputDecl() {
        ArrayList<VarDecl> inputDeclList = generateLustreDecl(freeInput);
        inputDeclList.addAll(generateLustreDecl(stateInput));
        return inputDeclList;
    }

    private ArrayList<VarDecl> generateLustreDecl(InputOutput stateInput) {
        return stateInput.generateVarDecl();
    }

    public ArrayList<VarDecl> generateOutputDecl() {
        return stateOutput.generateVarDecl();
    }

    /**
     * searches in all in input and output arrays to check if it is one in them
     * @param s
     * @return
     */
    public boolean isInOutVar(String s, NamedType type) {
        return isFreeInVar(s, type) || isStateInVar(s, type) || isStateOutVar(s, type) || isMethodOutVar(s, type);
    }


    public boolean isFreeInVar(String varName, NamedType type){
        return freeInput.contains(varName, type);
    }

    public boolean isStateInVar(String varName, NamedType type){
        return stateInput.contains(varName, type);
    }

    public boolean isStateOutVar(String varName, NamedType type){
        return stateOutput.contains(varName, type);
    }

    public boolean isMethodOutVar(String varName, NamedType type){
        return methodOutput.contains(varName, type);
    }

    public ArrayList<VarDecl> generaterMethodOutDeclList() {
        return methodOutput.generateVarDecl();
    }

}
