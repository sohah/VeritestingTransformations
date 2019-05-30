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
import jkind.api.results.Status;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.parsing.LustreParseUtil;
import org.eclipse.core.runtime.NullProgressMonitor;

import java.io.File;
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
            assert (synthesisContract != null);
            String synthesisContractStr = synthesisContract.toString();
            writeToFile(contractMethodName + "hole.lus", synthesisContractStr);

            JKindResult counterExResult = callJkind(contractMethodName + ".lus");
            System.out.println("JKIND: counter example contract call finished!");
            JKindResult synthesisResult = callJkind(contractMethodName + "hole.lus");
            System.out.println("JKIND: hole contract call finished!");

        }
        called = true;
        return null;
    }

    private static JKindResult callJkind(String fileName) {

        File file1 = new File(DiscoverContract.folderName + "/" + fileName);

        File file = new File("/Users/sohahussein/git/VeritestingTransformations/src/DiscoveryExamples/runPad_counter" +
                ".lus");
        /*ArrayList<String> properties = new ArrayList<>();
        properties.add("ok");

        final JKindResult jKindResult = new JKindResult(file.getName(), properties);

        new Thread("Discovery") {
            @Override
            public void run() {
                KindApi api = new JKindApi();
                api.setTimeout(10);
                api.execute(file, jKindResult, new NullProgressMonitor());
            }
        }.start();

        return jKindResult;*/

        return runJKind(file1);
    }

    private static JKindResult runJKind(File file) {
        JKindApi api = new JKindApi();
        JKindResult result = new JKindResult("");
        api.execute(file, result, new NullProgressMonitor());
        return result;
    }


    //ToDo: not sure if this works, I need to test the change.
    public static String toSMT(String solver, HashSet z3FunDecl) {
        return Z3Format.toSMT(solver, z3FunDecl);
    }
}
