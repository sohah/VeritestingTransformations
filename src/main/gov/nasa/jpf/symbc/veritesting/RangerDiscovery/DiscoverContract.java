package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.lustre.Node;

import java.util.ArrayList;

public class DiscoverContract {
    /**
     * name of the method we want to extract its contract.
     */
    public static boolean contractDiscoveryOn = false;

/***** begin of unused vars***/
    /**
     * currently unused because we assume we have a way to find the input and output.
     * This later needs to be changed to generalize it by looking only at the method
     * and the class of interest.
     */
    public static String contractMethodName;
    public static String className;
    public static String packageName;
/***** end of unused vars***/

    public final ArrayList<Node> discoverLusterContract(DynamicRegion dynamicRegion){

        Contract contract = new Contract();
        Node rNode = ToLutre.generateRnode(dynamicRegion, contract);
        Node rWrapper = ToLutre.generateRwrapper();

        ArrayList<Node> nodeList = new ArrayList<>();
        nodeList.add(rNode);
        nodeList.add(rWrapper);
        return nodeList;
    }
}
