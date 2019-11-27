package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension.LustreAstMapExtnVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension.RemoveRepairConstructVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair.MinimalRepairDriver;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.CounterExampleQuery;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.repair.HolePlugger;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair.FlattenNodes;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair.SketchVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.*;
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
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.callJkind;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.writeToFile;

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
                    assert false; //removed definition repair for now.
                //repairDef(dynRegion);
            }
            called = true;
        } catch (IOException e) {
            System.out.println("Unable to read specification file.! Aborting");
            assert false;
            e.printStackTrace();
        }

    }

    private static void repairSpec(DynamicRegion dynRegion) throws IOException {
        String fileName;

        if (Config.repairInitialValues)
            System.out.println("Repair includes initial values");
        else
            System.out.println("Repair does NOT include initial values");


        //print out the translation once, for very first time we hit linearlization for the method of
        // interest.
        Contract contract = new Contract();

        //this holds a repair which we might find, but it might not be a tight repair, in which case we'll have to
        // call on the other pair of thereExists and forAll queries for finding minimal repair.
        ARepairSynthesis ARepairSynthesis = null;
        HolePlugger holePlugger = new HolePlugger();
        Program originalProgram, flatExtendedPgm = null;
        Program inputExtendedPgm = null; // holds the original program with the extended lustre feature of the
        // "repair" construct

        NodeRepairKey originalNodeKey;

        if (Config.repairMode == RepairMode.LIBRARY) {

            inputExtendedPgm = LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(tFileName)),
                    "UTF-8"));

            originalNodeKey = defineNodeKeys(inputExtendedPgm);

            flatExtendedPgm = FlattenNodes.execute(inputExtendedPgm);

            originalProgram = RemoveRepairConstructVisitor.execute(flatExtendedPgm);

        } else {
            originalProgram = LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(tFileName)),
                    "UTF-8"));

            originalNodeKey = defineNodeKeys(originalProgram);

        }

        CounterExampleQuery counterExampleQuery = new CounterExampleQuery(dynRegion, originalProgram, contract);
        String counterExampleQueryStrStr = counterExampleQuery.toString();

        do {
            fileName = contractMethodName + "_" + loopCount + ".lus";
            writeToFile(fileName, counterExampleQueryStrStr, false);

            JKindResult counterExResult = callJkind(fileName, false, -1, false);
            switch (counterExResult.getPropertyResult(tnodeSpecPropertyName).getStatus()) {
                case VALID: //valid match
                    System.out.println("^-^Ranger Discovery Result ^-^");

                    if (loopCount > 0) {// we had at least a single repair/synthesis, at that point we want to find
                        // minimal repair.
                        System.out.print("Initial repair found, trying minimal repair.");
                        Program minimalRepair = MinimalRepairDriver.execute(counterExampleQuery.getCounterExamplePgm
                                        (), contract, originalProgram,
                                ARepairSynthesis, flatExtendedPgm);
                    } else
                        System.out.println("Contract Matching! Printing repair and aborting!");

                    //System.out.println(getTnodeFromStr(fileName));
                    DiscoverContract.repaired = true;
                    return;
                case INVALID: //synthesis is needed
                    if (ARepairSynthesis == null) {
                        Program holeProgram = null;
                        ArrayList<Hole> holes = null;
                        switch (Config.repairMode) {
                            case CONSTANT:
                                holeProgram = SpecConstHoleVisitor.executeMain(LustreParseUtil.program(originalProgram.toString()), originalNodeKey);
                                holes = new ArrayList<>(SpecConstHoleVisitor.getHoles());
                                break;
                            case PRE:
                                holeProgram = SpecPreHoleVisitor.executeMain(LustreParseUtil.program(originalProgram.toString()), originalNodeKey);
                                holes = new ArrayList<>(SpecPreHoleVisitor.getHoles());
                                break;
                            case LIBRARY:
                                holeProgram = LustreAstMapExtnVisitor.execute(flatExtendedPgm);
                                holes = new ArrayList<>(LustreAstMapExtnVisitor.getHoles());
                                break;
                            default:
                                assert false;
                        }
                        ARepairSynthesis = new ARepairSynthesis(contract, holeProgram, holes, counterExResult, originalNodeKey);
                    } else
                        ARepairSynthesis.collectCounterExample(counterExResult);

                    if (loopCount == 0) //first loop, then setup initial repair values
                        holeRepairState.createEmptyHoleRepairValues();

                    String synthesisContractStr = ARepairSynthesis.toString();
                    fileName = contractMethodName + "_" + loopCount + "_" + "hole.lus";
                    writeToFile(fileName, synthesisContractStr, false);

                    JKindResult synthesisResult = callJkind(fileName, false, ARepairSynthesis
                            .getMaxTestCaseK() - 2, false);
                    switch (synthesisResult.getPropertyResult(counterExPropertyName).getStatus()) {
                        case VALID:
                            System.out.println("^-^ Ranger Discovery Result ^-^");
                            System.out.println("Cannot find a synthesis");
                            DiscoverContract.repaired = false;
                            return;
                        case INVALID:
                            System.out.println("repairing holes for iteration#:" + loopCount);
                            if (Config.repairMode != RepairMode.LIBRARY) {
                                holeRepairState.plugInHoles(synthesisResult);
                                holePlugger.plugInHoles(synthesisResult, counterExampleQuery
                                        .getCounterExamplePgm
                                                (), ARepairSynthesis.getSynthesizedProgram(), ARepairSynthesis.getSynNodeKey());
                                counterExampleQueryStrStr = holePlugger.toString();
                                DiscoveryUtil.appendToFile(holeRepairFileName, holeRepairState.toString());
                                break;
                            } else {
                                inputExtendedPgm = SketchVisitor.execute(flatExtendedPgm, synthesisResult, false);
                                originalProgram = RemoveRepairConstructVisitor.execute(inputExtendedPgm);
                                fileName = contractMethodName + "_Extn" + loopCount + ".lus";
                                writeToFile(fileName, inputExtendedPgm.toString(), false);

                                counterExampleQuery = new CounterExampleQuery(dynRegion, originalProgram, contract);
                                counterExampleQueryStrStr = counterExampleQuery.toString();
                                break;
                            }
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
/*
    public static Program getLustreNoExt(Program origLustreExtPgm) {
        return RemoveRepairConstructVisitor.execute(origLustreExtPgm);

    }*/

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
