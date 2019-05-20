package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import jkind.lustre.Ast;
import jkind.lustre.NamedType;
import jkind.lustre.TupleType;
import jkind.lustre.VarDecl;

import java.util.ArrayList;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.*;

public class InOutManager {

    InputOutput freeInput = new InputOutput();
    InputOutput stateInput = new InputOutput();
    InputOutput stateOutput = new InputOutput();
    InputOutput methodOutput = new InputOutput();

    public void discoverVars(){
        discoverFreeInput();
        discoverStateInput();
        discoverStateOutput();
        discoverMethodOutput();
    }

    //entered by hand for now
    private void discoverMethodOutput() {
        methodOutput.add("r351.ignition_r.1.7.4", NamedType.INT);
    }

    //entered by hand for now
    private void discoverFreeInput(){
        freeInput.add("signal", NamedType.INT);
    }

    //entered by hand for now
    private void discoverStateInput(){
        stateInput.add("start_btn", NamedType.INT);
        stateInput.add("launch_btn", NamedType.INT);
        stateInput.add("ignition", NamedType.INT);
        stateInput.add("reset_btn", NamedType.INT);
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutput(){
        stateOutput.add("r351.start_btn.1.15.4", NamedType.INT);
        stateOutput.add("r351.launch_btn.1.17.4", NamedType.INT);
        stateOutput.add("r351.reset_btn.1.9.4", NamedType.INT);

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
