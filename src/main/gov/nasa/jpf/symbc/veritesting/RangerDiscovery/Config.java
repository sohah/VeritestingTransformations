package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import jkind.lustre.Ast;
import jkind.lustre.BoolExpr;
import jkind.lustre.IntExpr;

public class Config {
    public static String counterExPropertyName = "fail";
    public static String folderName = "../src/DiscoveryExamples/";
    static String tFileName;
    static String holeRepairFileName = folderName + "holeRepair";
    public static String TNODE = "T_node";
    public static String RNODE = "R_node";
    public static String WRAPPERNODE = "R_wrapper";
    public static String CHECKSPECNODE = "Check_spec";
    public static String H_discovery = "H_discovery";
    public static int loopCount = 0;
    public static boolean repairInitialValues = true;
    public static String specPropertyName = "ok";
    public static String tnodeSpecPropertyName;

    public static Ast defaultHoleValBool = new BoolExpr(false);
    public static Ast defaultHoleValInt = new IntExpr(1);
    public static boolean useInitialSpecValues = true;

    public static String spec = "pad";
    public static boolean defaultBoolValue = false;
    public static int initialIntValue = 0;

    public static void setup(){
        if(spec.equals("pad")){
            tFileName = folderName + "FaultyImaginaryPad";
            tnodeSpecPropertyName = "T_node~0.p1";
        } else if(spec.equals("even")){
            tFileName = folderName + "EvenOrigSpec";
            tnodeSpecPropertyName = "T_node~0.p1"; // we do not know yet!
        }else{
            System.out.println("unsupported spec, you need to setup input and output of the spec before usage!");
            assert false;
        }
    }
}
