package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractDiscoveryOn;

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



    public ArrayList<Variable> freeInput = new ArrayList<>();
    public ArrayList<Variable> stateInput = new ArrayList<>();
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
        freeInput.add(new IntVariable("signal", 0,10));
    }

    //entered by hand for now
    private void discoverStateInput(){
        stateInput.add(new IntVariable("start_btn", 0,10));
        stateInput.add(new IntVariable("launch_btn", 0,10));
        stateInput.add(new IntVariable("ignition_btn", 0,10));
        stateInput.add(new IntVariable("reset_btn", 0,10));
    }

    //entered by hand for now
    private void discoverStateOutput(){
        stateOutput.add(new IntVariable("ignition_btn", 0,10));
    }

    //entered by hand for now
    private void discoverOutput(){

    }


}
