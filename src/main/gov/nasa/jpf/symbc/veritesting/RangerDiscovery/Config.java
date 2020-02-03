package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import jkind.lustre.Ast;
import jkind.lustre.BoolExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.Program;

import java.io.File;
import java.io.IOException;

public class Config {
    public static String counterExPropertyName = "fail";
    public static String folderName = "../src/DiscoveryExamples/";
    static String tFileName;
    static String holeRepairFileName = folderName + "holeRepair";
    public static String TNODE = "T_node"; // also refers to the R_prime in the refinement loop.
    public static String RNODE = "Ranger_node";
    public static String WRAPPERNODE = "Ranger_wrapper";
    public static String CHECKSPECNODE = "Check_spec";
    public static String H_discovery = "H_discovery";
    public static String FIXED_T = "Fixed_T";
    public static String CAND_T_PRIME = "Candidate_T_Prime";
    public static String specPropertyName = "ok";
    public static String wrapperOutpuName = "out";

    public static String tnodeSpecPropertyName;

    public static String candidateSpecPropertyName = "discovery_out";

    public static Ast defaultHoleValBool = new BoolExpr(false);
    public static Ast defaultHoleValInt = new IntExpr(1);
    public static boolean useInitialSpecValues = true;

    //this boolean toggles between equation based repair and whole spec repair.
    public static boolean specLevelRepair;// = false;

    public static String spec;// = "even";

    public static String currFaultySpec;
    public static String[] faultySpecs;

    public static int faultySpecIndex = 0;

    public static boolean defaultBoolValue = false;
    public static int initialIntValue = 0;

    public static String methodReturnName = "result";

    public static Program auxilaryRepairProgram;

    public static String repairLustreFileName = "RepairLibrary";

    public static int costLimit = 10; // value entered by hand for now


    public static int faultyEquationNumber = 1;

    public static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.RepairMode repairMode;
    public static boolean repairInitialValues;

    //this contains specific equations we would like to repair, instead of repairing the whole thing. This is now used for testing only.
    public static Integer[] equationNumToRepair = {1};
    public static boolean allEqRepair = true;


    public static boolean canSetup() throws IOException {

        if ((faultySpecIndex) >= faultySpecs.length)
            return false;

        currFaultySpec = faultySpecs[faultySpecIndex];
        ++faultySpecIndex;

        tFileName = folderName + currFaultySpec;
        tnodeSpecPropertyName = "T_node~0.p1";

        //make a new directory for the output of that spec
        new File(folderName + "/output/" + Config.currFaultySpec).mkdirs();

        return true;
        /*if (spec.equals("pad")) {
            tFileName = folderName + "FaultyPreImaginaryPad";
        } else if (spec.equals("even")) {
            tFileName = folderName + "FaultyPreEvenSpec";
        } else if (spec.equals("wbs")) {
            tFileName = folderName + "FaultyImaginaryWBS"; //
        } else if (spec.equals("vote")) {
            tFileName = folderName + "vote"; //
        }*/
        /*else if (spec.equals("evenRestrictive")) {
            tFileName = folderName + "FaultyEvenRestrictiveSpec";
            tnodeSpecPropertyName = "T_node~0.p1"; // we do not know yet!
        } else if (spec.equals("FaultyPreEvenSpec")) {
            tFileName = folderName + "FaultyPreEvenSpec";
            tnodeSpecPropertyName = "T_node~0.p1"; // we do not know yet!
        } */
        /*else {
            System.out.println("unsupported spec, you need to setup input and output of the spec before usage!");
            assert false;
        }*/
/*
        auxilaryRepairProgram = LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(folderName +
                repairLustreFileName)), "UTF-8"));


        System.out.println(auxilaryRepairProgram);
*/
    }
}
