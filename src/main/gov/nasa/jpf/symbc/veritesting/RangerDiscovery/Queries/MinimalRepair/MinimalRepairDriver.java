package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension.NoExtLustreVisitor;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ARepairSynthesis;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.lustre.Program;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractMethodName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.writeToFile;

public class MinimalRepairDriver {

    private static Contract contract;
    private static Program repairedProgram;
    private static ARepairSynthesis lastSynthizedContract;

    public static int minimalLoopCount = 0;

    /**
     * This method initiates the discovery of finding minimal repair enclosed in the repairedProgram. It starts by
     * finding the there exist part of finding some R', then proceeds by calling the forall part to ensure that
     * indeed R' is inclosed in R and still matches the implementation.
     * @param repairedProgram this is the specification after repair, which we want to find some inner, enclosed
     *                        program.
     * @param lastSynthizedContract This is the last query used for the repaired program.
     * @return
     */

    public static Program execute(Program repairedProgram, ARepairSynthesis
            lastSynthizedContract) {
        MinimalRepairDriver.repairedProgram = repairedProgram;
        MinimalRepairDriver.lastSynthizedContract = lastSynthizedContract;

        //removing the repair expression keeping only the repair value included
        repairedProgram = NoExtLustreVisitor.execute(repairedProgram);

        MinimalRepairSynthesis rPrimeExistsQ = new MinimalRepairSynthesis(lastSynthizedContract, repairedProgram.getMainNode());

        String fileName = contractMethodName + "_" + minimalLoopCount + "_" + "rPrimeExists.lus";
        writeToFile(fileName, rPrimeExistsQ.toString());

        return rPrimeExistsQ.getSynthesizedProgram();
    }
}
