package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

public class Config {
    public static String counterExPropertyName = "fail";
    public static String folderName = "../src/DiscoveryExamples/";
    static String tFileName = folderName + "FaultyImaginaryPad";
    //static String tFileName = folderName + "EvenOrigSpec";
    static String holeRepairFileName = folderName + "holeRepair";
    public static String TNODE = "T_node";
    public static String RNODE = "R_node";
    public static String WRAPPERNODE = "R_wrapper";
    public static String CHECKSPECNODE = "Check_spec";
    public static String H_discovery = "H_discovery";
    public static int loopCount = 0;
    public static boolean repairInitialValues = true;
    public static String specPropertyName = "ok";
    public static String tnodeSpecPropertyName = "T_node~0.p1";

}
