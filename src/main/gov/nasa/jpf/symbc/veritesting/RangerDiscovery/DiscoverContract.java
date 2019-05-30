package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstHoleVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.SynthesisContract;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.SolverOption;
import jkind.api.JKindApi;
import jkind.api.KindApi;
import jkind.api.results.JKindResult;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.parsing.LustreParseUtil;
import org.eclipse.core.runtime.NullProgressMonitor;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
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

    //TODO: These needs to be configured using the .jpf file.
    public static String folderName = "../src/DiscoveryExamples/";
    static String tFileName = folderName + "ImaginaryPad";
    public static String TNODE = "T_node";
    public static String RNODE = "R_node";
    public static String WRAPPERNODE = "R_wrapper";

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

    public static final ArrayList<Node> discoverLusterContract(DynamicRegion dynRegion) {

        if (!called) { //print out the translation once, for very first time we hit linearlization for the method of
            // interest.
            CounterExContract counterExContract = new CounterExContract(dynRegion, tFileName);
            String counterExContractStr = counterExContract.toString();
            writeToFile(contractMethodName + ".lus", counterExContractStr);

            SynthesisContract synthesisContract = null;
            try {
                synthesisContract = new SynthesisContract(tFileName);
            } catch (IOException e) {
                System.out.println("problem occured while creating a synthesis contract! aborting!\n" + e.getMessage());
                assert false;
            }
            assert(synthesisContract != null);
            String synthesisContractStr = synthesisContract.toString();
            writeToFile(contractMethodName + "hole.lus", synthesisContractStr);

            JKindResult counterExResult = callJkind(counterExContractStr);
            System.out.println("JKIND: counter example contract call finished!");
            JKindResult synthesisResult = callJkind(synthesisContractStr);
            System.out.println("JKIND: hole contract call finished!");

        }
        called = true;
        return null;
    }

    private static JKindResult callJkind(String mergedContracts) {
        /*String[] jkindArgs = new String[5];
        jkindArgs[0] = "-jkind";
        jkindArgs[1] = folderName + contractMethodName + ".lus";
        jkindArgs[2] = "-solver";
        jkindArgs[3] = "z3";
        jkindArgs[4] = "-scratch";*/
        JKindApi jKindApi = new JKindApi();
        jKindApi.setSolver(SolverOption.Z3);
        jKindApi.setJKindJar("../lib/jkind.jar");
        ArrayList<String> propertiesToCheck = new ArrayList<String>();
        propertiesToCheck.add("ok");
        JKindResult jKindResult = new JKindResult("discovery", propertiesToCheck);

        new Thread("Analysis") {
            @Override
            public void run() {
                KindApi api = new JKindApi();
                api.setTimeout(10);
                api.execute(mergedContracts, jKindResult, new NullProgressMonitor());
            }
        }.start();

        return jKindResult;


    }


    //ToDo: not sure if this works, I need to test the change.
    public static String toSMT(String solver, HashSet z3FunDecl) {
        return Z3Format.toSMT(solver, z3FunDecl);
    }
}
