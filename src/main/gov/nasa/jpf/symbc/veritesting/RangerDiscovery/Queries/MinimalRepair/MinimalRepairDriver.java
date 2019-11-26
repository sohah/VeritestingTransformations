package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension.NoExtLustreVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ARepairSynthesis;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair.SketchVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.api.results.JKindResult;
import jkind.lustre.Node;
import jkind.lustre.Program;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractMethodName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.getLustreNoExt;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.callJkind;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.writeToFile;

public class MinimalRepairDriver {

    private static Contract contract;
    private static Program laskKnwnGoodRepairPgm; // last repair the matches the implementation.
    private static ARepairSynthesis lastSynthizedContract; // last query used to find the above repaired program

    private static Program counterExamplePgm;

    public static int minimalLoopCount = 0;

    /**
     * This method initiates the discovery of finding minimal repair enclosed in the repairedProgram. It starts by
     * finding the there exist part of finding some R', then proceeds by calling the forall part to ensure that
     * indeed R' is inclosed in R and still matches the implementation.
     *
     * @param counterExamplePgm
     * @param repairedProgram this is the specification after repair, which we want to find some inner, enclosed
     *                        program.
     * @param lastSynthizedContract This is the last query used for the repaired program.
     * @param flatExtendedPgm This is the program we started with that has the sketch extendion, repair construct, arround places we want to repair.
     * @return
     */

    public static Program execute(Program counterExamplePgm, Program repairedProgram, ARepairSynthesis
            lastSynthizedContract, Program flatExtendedPgm) {


        MinimalRepairDriver.counterExamplePgm = counterExamplePgm;
        MinimalRepairDriver.laskKnwnGoodRepairPgm = repairedProgram;
        MinimalRepairDriver.lastSynthizedContract = lastSynthizedContract;

        //removing the repair expression keeping only the repair value included
        laskKnwnGoodRepairPgm = NoExtLustreVisitor.execute(repairedProgram);

        MinimalRepairSynthesis tPrimeExistsQ = new MinimalRepairSynthesis(lastSynthizedContract, laskKnwnGoodRepairPgm.getMainNode());

        String fileName = contractMethodName + "_" + minimalLoopCount + "_" + "rPrimeExists.lus";
        writeToFile(fileName, tPrimeExistsQ.toString());



        JKindResult synthesisResult = callJkind(fileName, false, tPrimeExistsQ
                .getMaxTestCaseK() - 2);
        switch (synthesisResult.getPropertyResult(counterExPropertyName).getStatus()) {
            case VALID:
                System.out.println("^-^ Ranger Discovery Result ^-^");
                System.out.println("No more R' can be found, returning last known good repair.");
                return laskKnwnGoodRepairPgm; // returning the last known good repair.
            case INVALID:
                Program candTPrimePgm = getLustreNoExt(SketchVisitor.execute(flatExtendedPgm, synthesisResult));

                fileName = contractMethodName + "_" + minimalLoopCount + "_" + "rPrimeCandidate.lus";
                writeToFile(fileName, candTPrimePgm.toString());

                MinimalRepairCheck.execute(counterExamplePgm,getLustreNoExt(laskKnwnGoodRepairPgm).getMainNode(), candTPrimePgm.getMainNode());


                System.out.println("^-^ Ranger Discovery Result ^-^");
                System.out.println("No more R' can be found, returning last known good repair.");
                return laskKnwnGoodRepairPgm; // returning the last known good repair.
            default:
                System.out.println("^-^ Ranger Discovery Result ^-^");
                System.out.println("No more R' can be found, returning last known good repair.");
                return laskKnwnGoodRepairPgm; // returning the last known good repair.
        }
//            return rPrimeExistsQ.getSynthesizedProgram();
    }
}
