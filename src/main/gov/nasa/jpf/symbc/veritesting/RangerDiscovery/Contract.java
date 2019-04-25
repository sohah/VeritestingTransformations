package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;

import java.util.ArrayList;

public class Contract {

    Contract(){
        discoverVars();
    }

    /**
     * This method is used to collect the input of a method, later for contract discovery or for lustre translation.
     * currently unused
     */
    public void collectInput(){
        if(!contractDiscoveryOn){
            System.out.println("collectInput is valid only when contractDiscovery is turned on");
            assert false;
        }

    }



    public ArrayList<CloneableVariable> freeInput = new ArrayList<>();
    public ArrayList<CloneableVariable> stateInput = new ArrayList<>();
    public ArrayList<CloneableVariable> stateOutput = new ArrayList<>();
    public ArrayList<CloneableVariable> intermediateVar = new ArrayList<>();


    public void discoverVars(){
        discoverFreeInput();
        discoverStateInput();
        discoverStateOutput();
        discoverOutput();
    }

    //entered by hand for now
    private void discoverFreeInput(){
        freeInput.add(new WalaVarExpr())
    }

    //entered by hand for now
    private void discoverStateInput(){

    }

    //entered by hand for now
    private void discoverStateOutput(){

    }

    //entered by hand for now
    private void discoverOutput(){

    }


}
