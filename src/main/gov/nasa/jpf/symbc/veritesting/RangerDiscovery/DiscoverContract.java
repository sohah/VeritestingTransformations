package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.lustre.Node;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.writeToFile;

public class DiscoverContract {
    /**
     * name of the method we want to extract its contract.
     */
    public static boolean contractDiscoveryOn = false;
    public static boolean called = false;

    public static LinkedHashSet<Pair> z3QuerySet = new LinkedHashSet();


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

    public static final ArrayList<Node> discoverLusterContract(DynamicRegion dynamicRegion){

        if(!called) { //print out the translation once, for very first time we hit linearlization for the method of
            // interest.
            Contract contract = new Contract();
            Node rNode = ToLutre.generateRnode(dynamicRegion, contract);
            writeToFile(contractMethodName+".lus", rNode.toString());
            //System.out.println("^--^ printing lustre translation ^--^");
            //System.out.println(rNode);
        /*Node rWrapper = ToLutre.generateRwrapper();
        ArrayList<Node> nodeList = new ArrayList<>();
        nodeList.add(rNode);
        nodeList.add(rWrapper);
        return nodeList;*/
        }
        called = true;
        return null;
    }


    //ToDo: not sure if this works, I need to test the change.
    public static String toSMT(String solver, HashSet z3FunDecl){
        return Z3Format.toSMT(solver, z3FunDecl);
    }
}
