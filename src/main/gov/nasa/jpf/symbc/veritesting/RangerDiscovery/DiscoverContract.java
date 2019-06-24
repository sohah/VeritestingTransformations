package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.counterExample.CounterExContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repair.HolePlugger;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstHoleVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.HoleRepairState;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.SynthesisContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.TestCaseManager;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.api.JKindApi;
import jkind.api.results.JKindResult;
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
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.writeToFile;

public class DiscoverContract {
    /**
     * name of the method we want to extract its contract.
     */
    public static boolean contractDiscoveryOn = false;
    public static boolean called = false;

    public static LinkedHashSet<Pair> z3QuerySet = new LinkedHashSet();

    //TODO: These needs to be configured using the .jpf file.

    public static List<String> userSynNodes = new ArrayList<>();

    //public static HoleRepair holeRepairHolder = new HoleRepair();
    public static HoleRepairState holeRepairState = new HoleRepairState();


/***** begin of unused vars***/
    /**
     * currently unused because we assume we have a way to find the input and output.
     * This later needs to be changed to generalize it by looking only at the method
     * and the class of interest.
     */
    public static String contractMethodName;
    public static String className;
    public static String packageName;
    private static boolean repaired;

    /***** end of unused vars***/

    public static final void discoverLusterContract(DynamicRegion dynRegion) {
        String fileName;
        fillUserSynNodes();
        assert (userSynNodes.size() > 0);
        try {
            if (!called) { //print out the translation once, for very first time we hit linearlization for the method of
                // interest.
                Contract contract = new Contract();
                SynthesisContract synthesisContract = null;
                HolePlugger holePlugger = new HolePlugger();
                Program originalProgram;

                originalProgram = LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(tFileName)), "UTF-8"));
                NodeRepairKey originalNodeKey = defineNodeKeys(originalProgram);

                CounterExContract counterExContract = new CounterExContract(dynRegion, originalProgram, contract);
                String counterExContractStr = counterExContract.toString();

                do {
                    fileName = contractMethodName + loopCount + ".lus";
                    writeToFile(fileName, counterExContractStr);

                    JKindResult counterExResult = callJkind(fileName, false, -1);
                    switch (counterExResult.getPropertyResult(tnodeSpecPropertyName).getStatus()) {
                        case VALID: //valid match
                            System.out.println("^-^ Ranger Discovery Result ^-^");
                            System.out.println("Contract Matching! Printing repair and aborting!");
                            //System.out.println(getTnodeFromStr(fileName));
                            DiscoverContract.repaired = true;
                            return;
                        case INVALID: //synthesis is needed
                            if (synthesisContract == null) {
                                try {
                                    synthesisContract = new SynthesisContract(contract, originalProgram, counterExResult, originalNodeKey);
                                } catch (IOException e) {
                                    System.out.println("problem occured while creating a synthesis contract! aborting!\n" + e.getMessage());
                                    DiscoverContract.repaired = false;
                                    assert false;
                                }
                            } else
                                synthesisContract.collectCounterExample(counterExResult);

                            //holeRepairHolder.setHoleRepairMap(ConstHoleVisitor.getHoleToConstant());

                            if (Config.loopCount == 0) //first loop, then setup initial repair values
                                holeRepairState.createEmptyHoleRepairValues();

                            String synthesisContractStr = synthesisContract.toString();
                            fileName = contractMethodName + loopCount + "hole.lus";
                            writeToFile(fileName, synthesisContractStr);

                            JKindResult synthesisResult = callJkind(fileName, false, synthesisContract
                                    .getMaxTestCaseK() - 2);
                            switch (synthesisResult.getPropertyResult(counterExPropertyName).getStatus()) {
                                case VALID:
                                    System.out.println("^-^ Ranger Discovery Result ^-^");
                                    System.out.println("Cannot find a synthesis");
                                    DiscoverContract.repaired = false;
                                    return;
                                case INVALID:
                                    System.out.println("plugging in holes");
                                    holeRepairState.plugInHoles(synthesisResult);
                                    holePlugger.plugInHoles(synthesisResult, counterExContract
                                            .getCounterExamplePgm
                                                    (), synthesisContract.getSynthesisProgram(), synthesisContract.getSynNodeKey());
                                    counterExContractStr = holePlugger.toString();
                                    DiscoveryUtil.appendToFile(holeRepairFileName, holeRepairState.toString());
                                    break;
                                default:
                                    System.out.println("unexpected status for the jkind synthesis query.");
                                    DiscoverContract.repaired = false;
                                    assert false;
                                    break;
                            }
                            break;
                        default:
                            break;
                    }
                    ++loopCount;
                }
                while (true);
            }
            called = true;
        } catch (IOException e) {
            System.out.println("Unable to read specification file.! Aborting");
            assert false;
            e.printStackTrace();
        }

    }

    private static Node getTnodeFromStr(String tFileName) throws IOException {
        Program program = LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(folderName + "/" + tFileName)), "UTF-8"));

        List<Node> nodes = program.nodes;
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(TNODE))
                return nodes.get(i);
        }

        return null;
    }

    /**
     * Initiall node keys are defined on the original program, where the "main" is the only node that needs repair, as well as any other nodes that the user wants to define in userSynNodes
     *
     * @param program
     * @return
     */
    private static NodeRepairKey defineNodeKeys(Program program) {
        NodeRepairKey nodeRepairKey = new NodeRepairKey();
        nodeRepairKey.setNodesKey("main", NodeStatus.REPAIR);
        nodeRepairKey.setNodesKey(userSynNodes, NodeStatus.REPAIR);

        for (int i = 0; i < program.nodes.size(); i++) {
            Node node = program.nodes.get(i);
            if (!node.id.equals("main"))
                nodeRepairKey.setNodesKey(node.id, NodeStatus.DONTCARE_SPEC);
        }

        return nodeRepairKey;
    }

    private static void fillUserSynNodes() {
        userSynNodes.add("main");
    }


    private static JKindResult callJkind(String fileName, boolean kInductionOn, int maxK) {

        File file1 = new File(folderName + "/" + fileName);

        return runJKind(file1, kInductionOn, maxK);
    }

    private static JKindResult runJKind(File file, boolean kInductionOn, int maxK) {

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
        if (!kInductionOn)
            api.disableKInduction();

        if (maxK != -1) //if not set
            api.setN(maxK);

        api.disableSlicing();

        api.execute(file, result, new NullProgressMonitor());
        return result;
    }


    //ToDo: not sure if this works, I need to test the change.
    public static String toSMT(String solver, HashSet z3FunDecl) {
        return Z3Format.toSMT(solver, z3FunDecl);
    }


    public static boolean isRepaired() {
        return repaired;
    }
}
