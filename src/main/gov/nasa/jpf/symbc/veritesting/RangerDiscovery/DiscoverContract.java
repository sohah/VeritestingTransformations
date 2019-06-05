package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.counterExample.CounterExContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repair.HolePlugger;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstHoleVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.SynthesisContract;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.Main;
import jkind.api.ApiUtil;
import jkind.api.JKindApi;
import jkind.api.results.JKindResult;
import jkind.lustre.Ast;
import jkind.lustre.values.Value;
import org.eclipse.core.runtime.NullProgressMonitor;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
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
    static String holeRepairFileName = folderName + "holeRepair";
    public static String TNODE = "T_node";
    public static String RNODE = "R_node";
    public static String WRAPPERNODE = "R_wrapper";
    public static String CHECKSPECNODE = "Check_spec";
    public static String GLOBALYNODE = "H";

    public static HoleRepair holeRepairHolder = new HoleRepair();

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

    public static final void discoverLusterContract(DynamicRegion dynRegion) {

        if (!called) { //print out the translation once, for very first time we hit linearlization for the method of
            // interest.
            Contract contract = new Contract();
            SynthesisContract synthesisContract = null;
            HolePlugger holePlugger = null;

            CounterExContract counterExContract = new CounterExContract(dynRegion, tFileName, contract);
            String counterExContractStr = counterExContract.toString();

            do {
                writeToFile(contractMethodName + ".lus", counterExContractStr);

                JKindResult counterExResult = callJkind(contractMethodName + ".lus");
                switch (counterExResult.getPropertyResult("T_node~0.p1").getStatus()) {
                    case VALID: //valid match
                        System.out.println("Contract Matching! Aborting!");
                        return;
                    case INVALID: //synthesis is needed
                        if (synthesisContract == null) {
                            try {
                                synthesisContract = new SynthesisContract(contract, tFileName, counterExResult);
                            } catch (IOException e) {
                                System.out.println("problem occured while creating a synthesis contract! aborting!\n" + e.getMessage());
                                assert false;
                            }
                        } else
                            synthesisContract.collectCounterExample(counterExResult);

                        holeRepairHolder.setHoleRepairMap(ConstHoleVisitor.getHoleToConstant());

                        String synthesisContractStr = synthesisContract.toString();
                        writeToFile(contractMethodName + "hole.lus", synthesisContractStr);

                        JKindResult synthesisResult = callJkind(contractMethodName + "hole.lus");
                        switch (synthesisResult.getPropertyResult("ok").getStatus()) {
                            case VALID:
                                System.out.println("Cannot find a synthesis");
                                return;
                            case INVALID:
                                System.out.println("plugging in holes");
                                if(holePlugger == null)
                                    holePlugger = new HolePlugger(synthesisContract.getHoles());
                                holePlugger.plugInHoles(synthesisResult, counterExContract.getCounterExamplePgm(), synthesisContract.getSynthesisProgram());
                                counterExContractStr = holePlugger.toString();
                                DiscoveryUtil.appendToFile(holeRepairFileName, holeRepairHolder.toString());
                                break;
                            default:
                                System.out.println("unexpected status for the jkind synthesis query.");
                                assert false;
                                break;
                        }
                        break;
                    default:
                        break;
                }
            }
            while (true);
        }
        called = true;
    }


    private static JKindResult callJkind(String fileName) {

        File file1 = new File(DiscoverContract.folderName + "/" + fileName);

        return runJKind(file1);
    }

    private static JKindResult runJKind(File file) {

/*
        String[] jkindArgs = new String[5];

        jkindArgs[0] = "-jkind";
        jkindArgs[1] = folderName + contractMethodName + ".lus";
        jkindArgs[2] = "-solver";
        jkindArgs[3] = "z3";
        jkindArgs[4] = "-scratch";
        Main.main(jkindArgs);
*/

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
