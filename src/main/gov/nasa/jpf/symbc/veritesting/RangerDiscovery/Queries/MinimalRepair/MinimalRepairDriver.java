package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension.RemoveRepairConstructVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ARepairSynthesis;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair.SketchVisitor;
import jkind.api.results.JKindResult;
import jkind.lustre.Program;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractMethodName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.callJkind;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.writeToFile;

public class MinimalRepairDriver {

    private static Contract contract;
    private static Program laskKnwnGoodRepairPgm; // last repair the matches the implementation.
    private static ARepairSynthesis lastSynthizedContract; // last query used to find the above repaired program

    private static Program counterExamplePgm;

    public static int minimalLoopCount = 0;

    public static int minimalRepairLoopCount = -1;

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


        MinimalRepairDriver.counterExamplePgm = counterExamplePgm;
        MinimalRepairDriver.laskKnwnGoodRepairPgm = repairedProgram;
        MinimalRepairDriver.lastSynthizedContract = lastSynthizedContract;
        MinimalRepairDriver.contract = contract;

        /*//removing the repair expression keeping only the repair value included
        laskKnwnGoodRepairPgm = RemoveRepairConstructVisitor.execute(repairedProgram);
*/
        MinimalRepairSynthesis tPrimeExistsQ = new MinimalRepairSynthesis(lastSynthizedContract, laskKnwnGoodRepairPgm.getMainNode());


        while (true) {
            System.out.println("Trying minimal repair iteration #: " + minimalLoopCount);

            String fileName = contractMethodName + "_" + minimalLoopCount + "_" + "rPrimeExists.lus";
            writeToFile(fileName, tPrimeExistsQ.toString(), true);


            JKindResult synthesisResult = callJkind(fileName, false, tPrimeExistsQ
                    .getMaxTestCaseK() - 2, true);
            switch (synthesisResult.getPropertyResult(counterExPropertyName).getStatus()) {
                case VALID:
                    System.out.println("^-^ Ranger Discovery Result ^-^");
                    System.out.println("No more R' can be found, last known good repair was found at, outer loop # = " +
                            DiscoverContract.outerLoopRepairNum + " minimal repair loop # = " + minimalRepairLoopCount);
                    return laskKnwnGoodRepairPgm; // returning the last known good repair.
                case INVALID:
                    Program candTPrimePgm = RemoveRepairConstructVisitor.execute(SketchVisitor.execute(flatExtendedPgm, synthesisResult, true));

                    fileName = contractMethodName + "_" + minimalLoopCount + "_" + "rPrimeCandidate.lus";
                    writeToFile(fileName, candTPrimePgm.toString(), true);

                    Program forAllQ = MinimalRepairCheck.execute(contract, counterExamplePgm, laskKnwnGoodRepairPgm.getMainNode(), candTPrimePgm.getMainNode());

                    fileName = contractMethodName + "_" + minimalLoopCount + "_" + "forAllMinimal.lus";
                    writeToFile(fileName, ToLutre.lustreFriendlyString(forAllQ.toString()), true);

                    JKindResult counterExampleResult = callJkind(fileName, false, -1, true);

                    switch (counterExampleResult.getPropertyResult(candidateSpecPropertyName).getStatus()) {
                        case VALID:
                            laskKnwnGoodRepairPgm = candTPrimePgm;
                            minimalRepairLoopCount = minimalLoopCount; //storing the current loop count where a
                            System.out.print("Great! a tighter repair was found at, outer loop # = " +
                                    DiscoverContract.outerLoopRepairNum + " minimal repair loop # = " + minimalRepairLoopCount);

                            // minimal repair was found.
                            return candTPrimePgm;
                        case INVALID:
                            tPrimeExistsQ.collectCounterExample(counterExampleResult, tPrimeExistsQ.getSynthesizedProgram().getMainNode());
                            //Program newSynthesis = tPrimeExistsQ.getSynthesizedProgram();
                            ++minimalLoopCount;
                            break;
                        default:
                            System.out.println("^-^ Ranger Discovery Result ^-^");
                            System.out.println("Unknown solver output, No more R' can be found, returning last known good repair.");
                            return laskKnwnGoodRepairPgm; // returning the last known good repair.
                    }
                    break;
                default:
                    System.out.println("^-^ Ranger Discovery Result ^-^");
                    System.out.println("Unknown solver output , No more R' can be found, returning last known good repair.");
                    return laskKnwnGoodRepairPgm; // returning the last known good repair.
            }
//            return rPrimeExistsQ.getSynthesizedProgram();
        }
    }
}
