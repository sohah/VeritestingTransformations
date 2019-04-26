package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import jkind.lustre.Ast;
import jkind.lustre.VarDecl;

import java.util.ArrayList;

public class InOutManager {

    InputOutput freeInput = new InputOutput();
    InputOutput stateInput = new InputOutput();
    InputOutput stateOutput = new InputOutput();


    public void discoverVars(){
        discoverFreeInput();
        discoverStateInput();
        discoverStateOutput();
        discoverOutput();
    }

    //entered by hand for now
    private void discoverFreeInput(){
        freeInput.add("signal", Type.INT);
    }

    //entered by hand for now
    private void discoverStateInput(){
        stateInput.add("start_btn", Type.INT);
        stateInput.add("launch_btn", Type.INT);
        stateInput.add("ignition_btn", Type.INT);
        stateInput.add("reset_btn", Type.INT);
    }

    //entered by hand for now - order is important, needs to match in order of the input
    private void discoverStateOutput(){
        stateOutput.add("r347.start_btn.1.15.4", Type.INT);
        stateOutput.add("r347.launch_btn.1.17.4", Type.INT);
        stateOutput.add("r347.ignition_r.1.7.4", Type.INT);
        stateOutput.add("r347.reset_btn.1.9.4", Type.INT);

    }

    //entered by hand for now
    private void discoverOutput(){
        stateOutput.add("w12$1", Type.INT);
    }

    public ArrayList<VarDecl> generateInputDecl() {
        ArrayList<Ast> inputDeclList = generateLustreDecl(freeInput);
        inputDeclList.addAll(generateLustreDecl(stateInput));
        return inputDeclList;
    }

    private ArrayList<Ast> generateLustreDecl(InputOutput stateInput) {
        return generateLustreDecl(stateOutput);
    }

    public ArrayList<VarDecl> generateOutputDecl() {


        return null;
    }
}
