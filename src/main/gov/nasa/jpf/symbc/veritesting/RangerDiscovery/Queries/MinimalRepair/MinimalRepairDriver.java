package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension.RemoveRepairConstructVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ARepairSynthesis;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair.SketchVisitor;
import jkind.api.results.JKindResult;
import jkind.lustre.Node;
import jkind.lustre.Program;

import java.util.ArrayList;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.callJkind;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.writeToFile;

public class MinimalRepairDriver {

    private static Program laskKnwnGoodRepairPgm; // last repair the matches the implementation.
    //private static ARepairSynthesis lastSynthizedContract; // last query used to find the above repaired program

    //private static Program counterExamplePgm;

    public static int candidateLoopCount = 0; //counts the candidates attempted inside every tightness loop.

    public static int knownRepairLoopCount = 0; // counts how many tight repairs we needed to do.

    public static int successfulCandidateNum = -1;

    public static int lastKnownRepairLoopCount = -1;

    public static ArrayList<Node> repairs = new ArrayList<>();

    private static long thereExistsTime;

    private static long forAllTime;

    public static void resetState() {
        laskKnwnGoodRepairPgm = null;
        candidateLoopCount = 0;
        knownRepairLoopCount = 0;
        successfulCandidateNum = -1;
        lastKnownRepairLoopCount = -1;
        repairs = new ArrayList<>();
        thereExistsTime = 0;
        forAllTime = 0;
    }

    /**
     * This method initiates the discovery of finding minimal repair enclosed in the repairedProgram. It starts by
     * finding the there exist part of finding some R', then proceeds by calling the forall part to ensure that
     * indeed R' is inclosed in R and still matches the implementation.
     *
     * @param counterExamplePgm
     * @param contract
     * @param repairedProgram       this is the specification after repair, which we want to find some inner, enclosed
     *                              program.
     * @param lastSynthizedContract This is the last query used for the repaired program.
     * @param flatExtendedPgm       This is the program we started with that has the sketch extendion, repair construct, arround places we want to repair.    @return
     */

    public static Program execute(Program counterExamplePgm, Contract contract, Program repairedProgram, ARepairSynthesis
            lastSynthizedContract, Program flatExtendedPgm) {


        repairs.add(repairedProgram.getMainNode());

        //MinimalRepairDriver.counterExamplePgm = counterExamplePgm;
        MinimalRepairDriver.laskKnwnGoodRepairPgm = repairedProgram;

        /*//removing the repair expression keeping only the repair value included
        laskKnwnGoodRepairPgm = RemoveRepairConstructVisitor.execute(repairedProgram);
*/
        Program forAllQ;

        boolean canFindMoreTighterRepair = true;
        boolean tighterRepairFound = false;

        long singleQueryTime;

        MinimalRepairSynthesis tPrimeExistsQ = new MinimalRepairSynthesis(lastSynthizedContract, laskKnwnGoodRepairPgm.getMainNode());

        while (canFindMoreTighterRepair) {//we are still trying to discover a minimal repair, thus there is a potiential tighter repair that we haven't discovered so far.

            System.out.println("trying minimal good repair iteration #: " + knownRepairLoopCount);

            while (!tighterRepairFound && canFindMoreTighterRepair) { //while we haven't found a tighter repair and we know that we can find a tighter repair.
                System.out.println("Trying candidate #: " + candidateLoopCount);

                String fileName = currFaultySpec + "_" + knownRepairLoopCount + "_" + candidateLoopCount + "_" + "rPrimeExists.lus";
                writeToFile(fileName, tPrimeExistsQ.toString(), true);

                System.out.println("ThereExists Query of : " + fileName );

                singleQueryTime = System.currentTimeMillis();
                JKindResult synthesisResult = callJkind(fileName, false, (tPrimeExistsQ
                        .getMaxTestCaseK() - 2), true, true);

                singleQueryTime = (System.currentTimeMillis() - singleQueryTime) / 1000;

                //System.out.println("TIME of ThereExists Query of : " + fileName + "= " + singleQueryTime);
                System.out.println("TIME = " + singleQueryTime);

                switch (synthesisResult.getPropertyResult(counterExPropertyName).getStatus()) {
                    case VALID:
                        System.out.println("^-^ Ranger Discovery Result ^-^");
                        System.out.println("No more R' can be found, last known good repair was found at, outer loop # = " +
                                DiscoverContract.outerLoopRepairNum + " minimal repair loop # = " + lastKnownRepairLoopCount);
                        canFindMoreTighterRepair = false;
                        break;
                    case INVALID:
                        Program candTPrimePgm = RemoveRepairConstructVisitor.execute(SketchVisitor.execute(flatExtendedPgm, synthesisResult, true));

                        fileName = currFaultySpec + "_" + knownRepairLoopCount + "_" + candidateLoopCount + "_" +
                                "rPrimeCandidate.lus";
                        writeToFile(fileName, candTPrimePgm.toString(), true);

                        forAllQ = MinimalRepairCheck.execute(contract, counterExamplePgm, laskKnwnGoodRepairPgm.getMainNode(), candTPrimePgm.getMainNode());

                        fileName = currFaultySpec + "_" + knownRepairLoopCount + "_" + candidateLoopCount + "_" + "forAllMinimal" +
                                ".lus";
                        writeToFile(fileName, ToLutre.lustreFriendlyString(forAllQ.toString()), true);


                        singleQueryTime = System.currentTimeMillis();

                        System.out.println("ForAll Query of : " + fileName);

                        JKindResult counterExampleResult = callJkind(fileName, true, -1, true, false);

                        singleQueryTime = (System.currentTimeMillis() - singleQueryTime) / 1000;

                        //System.out.println("TIME of forAll Query of : " + fileName + "= " + singleQueryTime);
                        System.out.println("TIME = " + singleQueryTime);

                        switch (counterExampleResult.getPropertyResult(candidateSpecPropertyName).getStatus()) {
                            case VALID:
                                laskKnwnGoodRepairPgm = candTPrimePgm;
                                successfulCandidateNum = candidateLoopCount; //storing the current loop count where a
                                lastKnownRepairLoopCount = knownRepairLoopCount; // storing the loop number at which
                                if (!containsNode(repairs, candTPrimePgm.getMainNode())) {
                                    repairs.add(candTPrimePgm.getMainNode());
                                    // the last good tight repair was found.
                                    System.out.println("Great! a tighter repair was found at, outer loop # = " + DiscoverContract.outerLoopRepairNum + " minimal repair loop # = " + lastKnownRepairLoopCount + " successful candidate # = " + successfulCandidateNum);

                                    // minimal repair was found.
                                    tighterRepairFound = true;
                                    break;
                                } else {
                                    System.out.println("encountering the same repair, aborting.");
                                    canFindMoreTighterRepair = false;
                                    break;
                                }
                            case INVALID:
                                tPrimeExistsQ.collectCounterExample(counterExampleResult, tPrimeExistsQ.getSynthesizedProgram().getMainNode());
                                ++candidateLoopCount;
                               /* if(candidateLoopCount == 30) //exit if we tried 30 candidates.
                                    canFindMoreTighterRepair=false;*/
                                break;
                            default:
                                System.out.println("^-^ Ranger Discovery Result ^-^");
                                System.out.println("Unknown solver output, No more R' can be found, returning last known good repair.");
                                canFindMoreTighterRepair = false;
                                break;
                        }
                        break;
                    default:
                        System.out.println("^-^ Ranger Discovery Result ^-^");
                        System.out.println("Unknown solver output , No more R' can be found, returning last known good repair.");
                        canFindMoreTighterRepair = false;
                        break;
                }
            }
            //there are two conditions where this can be reached, either we have found a tighter repair, in which can
            // we want to find the minimal, or we have found out that there is no more tighter repairs could be found
            // and so we'd just abort the whole thing.
            if (tighterRepairFound) {
                tPrimeExistsQ.changeFixedR(laskKnwnGoodRepairPgm.getMainNode());
                tighterRepairFound = false;
                ++knownRepairLoopCount;
                candidateLoopCount = 0;
            }
        }

        System.out.println("Minimal repair finished with the following result, outer loop # = " + DiscoverContract.outerLoopRepairNum +
                " minimal repair loop # = " + lastKnownRepairLoopCount + " the LAST candidate repair loop # = " + successfulCandidateNum);
        return laskKnwnGoodRepairPgm;
    }


    //unfortungely we will do string comparision since node does not implement isEqual method.
    private static boolean containsNode(ArrayList<Node> repairs, Node mainNode) {
        for (Node node : repairs) {
            if (node.toString().equals(mainNode.toString()))
                return true;
        }
        return false;
    }
}
