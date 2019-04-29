package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.SpecInOutManager;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractDiscoveryOn;

public class Contract {

    public final InOutManager rInOutManager = new InOutManager();
    public final SpecInOutManager tInOutManager = new SpecInOutManager();

    Contract(){
        rInOutManager.discoverVars();
        tInOutManager.discoverVars();
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

}
