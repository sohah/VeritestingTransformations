package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

public class JkindContract {

    public static ArrayList<String> jkindInVar = new ArrayList<>();
    public static ArrayList<String> jkindOutVar = new ArrayList<>();

    public static HashMap<String, String> jkindTypeTable = new HashMap<>();

    private static String jKindFile = "../../../ContractDiscoveryProjects/RunPadModel/ImaginaryPad/ImaginaryPad.k-induction.smt2";


    public static void discoverJKindVars() { //this really should automatically collect the inputs from the jkind file.
        //TODO: I need to have a means to obtain this set.
        jkindInVar.add("sig");
        jkindInVar.add("ignition");
        jkindInVar.add("launch_bt");
        jkindInVar.add("reset_flag");
        jkindInVar.add("start_bt");


        jkindTypeTable.put("sig", "int");


        jkindOutVar.add("ignition");
        jkindOutVar.add("launch_bt");
        jkindOutVar.add("reset_flag");
        jkindOutVar.add("start_bt");
    }

    public static String getJkindTransition() {
        try {
            return DiscoveryUtility.readFileToString(jKindFile);
        } catch (IOException e) {
            System.out.println("problem while trying to read the jkind query.");
            return null;
        }
    }




}
