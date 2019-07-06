package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.SubstitutionVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.CandidateRepairExpr;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.CandidateSelectionMgr;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders.FaultyEquation;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.counterExample.CounterExContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.repair.HolePlugger;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.HoleRepairState;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.SpecConstHoleVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.SynthesisContract;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.api.results.JKindResult;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.parsing.LustreParseUtil;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.callJkind;
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
    public static HoleRepairState holeRepairState;

    public static FaultyEquation faultyEquation;

    public static int loopCount = 0;
    public static int permutationCount = 0;

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
        fillUserSynNodes();
        try {
            Config.setup();
            assert (userSynNodes.size() > 0);
            if (!called) {
                if (Config.specLevelRepair)
                    repairSpec(dynRegion);
                else
                    repairDef(dynRegion);
            }
            called = true;
        } catch (IOException e) {
            System.out.println("Unable to read specification file.! Aborting");
            assert false;
            e.printStackTrace();
        }

    }

    private static void repairDef(DynamicRegion dynRegion) throws IOException {
        String fileName;


        //print out the translation once, for very first time we hit linearlization for the method of
        // interest.
        Contract contract = new Contract();
        Program pgmT;

        pgmT = LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(tFileName)), "UTF-8"));
        NodeRepairKey originalNodeKey = defineNodeKeys(pgmT);


        do {
            CounterExContract counterExContract = new CounterExContract(dynRegion, pgmT, contract);
            String counterExContractStr = counterExContract.toString();

            fileName = contractMethodName + permutationCount + "_" + loopCount + ".lus";
            //JKindResult counterExResult = CounterExContract.search(fileName, pgmT, rNode, rWrapper);
            writeToFile(fileName, counterExContractStr);

            JKindResult counterExResult = callJkind(fileName, false, -1);

            switch (counterExResult.getPropertyResult(tnodeSpecPropertyName).getStatus()) {
                case VALID: //valid match
                    System.out.println("^-^ Ranger Discovery Result ^-^");
                    System.out.println("Contract Matching! Printing repair and aborting!");
                    DiscoverContract.repaired = true;
                    return;
                case INVALID: //synthesis is needed
                    faultyEquation = Config.getFaultyEquation(pgmT);
                    assert (faultyEquation != null);
                    holeRepairState = new HoleRepairState();
                    CandidateSelectionMgr candidateSelectionMgr = new CandidateSelectionMgr();
                    while (candidateSelectionMgr.queueSize() > 0) {
                        loopCount = 0; //resetting loopCount.
                        CandidateRepairExpr candidateExpr = candidateSelectionMgr.poll();
                        HolePlugger holePlugger = new HolePlugger();
                        boolean candidateRepairFailed = false;
                        SynthesisContract synthesis = null;

                        while (!candidateRepairFailed) {
                            if (synthesis == null) {
                                //try {
                                //separating the creation of the hole program from the Synthesis of the contract.
                                Program holeProgram = SubstitutionVisitor.substitute(pgmT, candidateExpr, faultyEquation);

                                synthesis = new SynthesisContract(contract, holeProgram, new ArrayList(candidateExpr.getHoleMap().keySet()), counterExResult, originalNodeKey);
                                //} catch (IOException e) {
                                //System.out.println("problem occurred while creating a synthesis contract! aborting!\n" + e.getMessage());
                                //                    DiscoverContract.repaired = false;
                                //                    assert false;
                                //}
                            } else
                                synthesis.collectCounterExample(counterExResult);

                            if (loopCount == 0) //first loop, then setup initial repair values
                                holeRepairState.createEmptyHoleRepairValues();

                            String synthesisContractStr = synthesis.toString();
                            fileName = contractMethodName + permutationCount + "_" + loopCount + "hole.lus";
                            writeToFile(fileName, synthesisContractStr);

                            JKindResult synthesisResult = callJkind(fileName, false, synthesis
                                    .getMaxTestCaseK() - 2);
                            switch (synthesisResult.getPropertyResult(counterExPropertyName).getStatus()) {
                                case VALID:
                                    System.out.println("^-^ Ranger Discovery Result ^-^");
                                    System.out.println("Cannot find a synthesis. Trying a different permutation.");
                                    candidateRepairFailed = true;
                                    break;
                                case INVALID:
                                    System.out.println("repairing holes for iteration#:" + loopCount);
                                    holeRepairState.plugInHoles(synthesisResult);
                                    holePlugger.plugInHoles(synthesisResult, counterExContract
                                            .getCounterExamplePgm
                                                    (), synthesis.getSynthesisProgram(), synthesis.getSynNodeKey());
                                    counterExContractStr = holePlugger.toString();
                                    DiscoveryUtil.appendToFile(holeRepairFileName, holeRepairState.toString());
                                    break;
                                default:
                                    System.out.println("unexpected status for the jkind synthesis query.");
                                    DiscoverContract.repaired = false;
                                    assert false;
                                    break;
                            }
                            ++loopCount;
                            ++permutationCount;
                        }
                    }
                    System.out.print("No more candidate hole expression to use. No repair! Aborting");
                    return;
                default:
                    break;
            }
        }
        while (true);
    }


    private static void repairSpec(DynamicRegion dynRegion) throws IOException {
        String fileName;

        //print out the translation once, for very first time we hit linearlization for the method of
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
                        Program holeProgram = SpecConstHoleVisitor.executeMain(LustreParseUtil.program(originalProgram.toString()), originalNodeKey);
                        ArrayList<Hole> holes = new ArrayList<>(SpecConstHoleVisitor.getHoles());
                        synthesisContract = new SynthesisContract(contract, holeProgram, holes, counterExResult, originalNodeKey);
                    } else
                        synthesisContract.collectCounterExample(counterExResult);

                    if (loopCount == 0) //first loop, then setup initial repair values
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
                            System.out.println("repairing holes for iteration#:" + loopCount);
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


    //ToDo: not sure if this works, I need to test the change.
    public static String toSMT(String solver, HashSet z3FunDecl) {
        return Z3Format.toSMT(solver, z3FunDecl);
    }


    public static boolean isRepaired() {
        return repaired;
    }
}
