//package Launch;
package AnRocketLaunch;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

class AnMainSymbolic {

    private static boolean makeStep(PadUnitManager padUnitManager, int padNumber, int rocketAction, int rocketNumber, boolean actionIsTimeout) throws InvalidInputException {

        if (padNumber >= 0 && padNumber < 7) {
            if (rocketAction == 1) {
                padUnitManager.takeAction(padNumber, rocketNumber);
                return true;

            } else {
                controller.takeAction(padUnitManager.padArray, padNumber, rocketNumber, rocketAction, actionIsTimeout);
                return false;
            }
        } else return false;
    }

    public static boolean checkPadNumber(String inputNumOfPad, String padNumber) {
        int NumberOfPad = Integer.parseInt(inputNumOfPad);
        for (int k = 0; k <= NumberOfPad; k++) {
            boolean rightPadNum = padNumber.equals(Integer.toString(k));
            if (rightPadNum) {
                return true;
            }
        }
        return false;
    }

    public static boolean checkInputRocketNumber(String rocketNum) {
        boolean rocketNumEqual1 = (!rocketNum.equals("1"));
        boolean rocketNumEqual2 = (!rocketNum.equals("2"));
        if (rocketNumEqual1 && rocketNumEqual2) {
            return false;
        }
        return true;
    }


    public static void terminateInstruction() {
        System.out.println("TERMINATE THE PROCESS ANYTIME BY ENTERING '0'");
        System.out.println("TERMINATE THE PROCESS ANYTIME BY ENTERING '0'");
        System.out.println("TERMINATE THE PROCESS ANYTIME BY ENTERING '0'");
    }

    public static void println() {
        System.out.println("------------------------------------------------");
    }

    public static Controller controller = new Controller();

    public static void main(String[] args) throws IOException, InvalidInputException {
        String rocketInfo = "";
        int MaxPad = 8;
        String action;
        terminateInstruction();
        println();
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        boolean notHaltProgram1 = true;
        boolean notHaltProgram2 = true;
        int intNumOfPad = 0;
        int padNumber = 0;
        int rocketNumber = 0;
        int rocketAction = 0;
        String inputPadName = "";
        boolean actionIsActivate = false;
        int inputNumOfPad = 8;
        PadUnitManager padUnitManager = new PadUnitManager(8);

        boolean ActionIsTimeout = false;

        try {
            padUnitManager = new PadUnitManager(inputNumOfPad);
        } catch (InvalidInputException e) {
            e.printStackTrace();
        }
        try {

            actionIsActivate = makeStep(padUnitManager, padNumber, rocketAction, rocketNumber, ActionIsTimeout);

        } catch (InvalidInputException e) {
            System.out.println(e);
        }
    }
}
