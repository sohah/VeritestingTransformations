//package Launch;
package AnRocketLaunch;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

class AnMainSymbolic {

    public static String readInputStreamWithTimeout(InputStream is, byte[] b, int timeoutMillis, PadUnit[] padArray, String padInfo, String rocketInfo)
            throws IOException {
        int PadNumber = Integer.parseInt(padInfo);
        PadUnit pad = padArray[PadNumber];
        int rocketName = Integer.parseInt(rocketInfo);
        int bufferOffset = 0;
        long maxTimeMillis = System.currentTimeMillis() + timeoutMillis;
        String action = "";
        boolean notReceiveInput = true;
        while (System.currentTimeMillis() < maxTimeMillis && bufferOffset < b.length && notReceiveInput) {
            int readLength = java.lang.Math.min(is.available(), b.length - bufferOffset);
            // can alternatively use bufferedReader, guarded by isReady():
            int readResult = is.read(b, bufferOffset, readLength);
            bufferOffset += readResult;
            if (bufferOffset != 0) {
                notReceiveInput = false;
            }
        }
        action = new String(b);
        if (notReceiveInput == true) {
            controller.reset(pad, rocketName);
            return ("Time out case");
        }
        String result = "";
        int actionLength = action.length();
        for (int k = 0; k < actionLength; k++) {

            if (Character.isDigit(action.charAt(k))) {
                result += action.charAt(k);
            }
        }
        return result;
    }

    private static void ExceptionInputCase(int result) throws InvalidInputException {
        if (result == 5) {
            throw new InvalidInputException("Launch button is inactive unavaiable now");
        }
        if (result == 6) {
            throw new InvalidInputException("armed button is unavaiable now");
        }
        if (result == 17) {
            throw new InvalidInputException("Control Buttons are activated already");
        }
    }

    private static int makeStep(PadUnitManager padUnitManager, int rocketAction, int intNumOfPad, int padNumber, int rocketNumber, boolean actionIsTimeout) throws InvalidInputException {

        if ((intNumOfPad > padNumber) && (padNumber > 0)) {
            if (rocketAction == 1) {//action is activate
                return (padUnitManager.takeAction(intNumOfPad, padNumber, rocketNumber) + 10);
            } else {
                if ((rocketNumber == 1) || (rocketNumber == 2))
                    return controller.takeAction(intNumOfPad, padUnitManager.padArray, padNumber, rocketNumber, rocketAction, actionIsTimeout);
            }
        }
        return 5;
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

    /**
     * This method gets the current state of the pad and displays possible actions on the pad.
     *
     * @param rocketName
     * @param padArray
     * @param inputPadName
     * @param inputNumOfPad
     * @throws InvalidInputException
     */
    public static void CheckPadNameAndRocketNumberThenInputRocketAction(String rocketName, PadUnit[] padArray, String inputPadName, String inputNumOfPad) throws InvalidInputException
    //Check input padName and rocketInfo
    {
        if (checkPadNumber(inputNumOfPad, inputPadName) == false) {
            throw new InvalidInputException("This Pad is not registered");
        } else {
            if (checkInputRocketNumber(rocketName) == false) {
                throw new InvalidInputException("Rocket number can only be 1 or 2");
            } else {
                int rocketNumber = Integer.parseInt(rocketName);
                int padNumber = Integer.parseInt(inputPadName);
                ControlButtonState currentState;
                if (rocketNumber == 1) {
                    currentState = controller.map.get(padArray[padNumber]).getState1();
                } else {
                    currentState = controller.map.get(padArray[padNumber]).getState2();
                }
                if (currentState == ControlButtonState.armedLaunchAvailable) {
                    System.out.println("Input2: Enter action (only 2('armed') and 4('reset') are available)");
                } else if (currentState == ControlButtonState.inactive) {
                    System.out.println("Input2: Enter action (only 1('activate') and 4('reset') are available)");
                } else if (currentState == ControlButtonState.launchAvailable) {
                    System.out.println("Input2: Enter action (only 2('armed'), 3('launch') and 4('reset') are available)");
                }
            }
        }
    }

    public static void terminateInstruction() {
        System.out.println("TERMINATE THE PROCESS ANYTIME BY ENTERING '0'");
        System.out.println("TERMINATE THE PROCESS ANYTIME BY ENTERING '0'");
        System.out.println("TERMINATE THE PROCESS ANYTIME BY ENTERING '0'");
    }

    public static void println() {
        System.out.println("------------------------------------------------");
    }

    public static boolean actionValidity(String action) {
        boolean actionIs0 = action.equals("0");
        boolean actionIs1 = action.equals("1");
        boolean actionIs2 = action.equals("2");
        boolean actionIs3 = action.equals("3");
        boolean actionIs4 = action.equals("4");
        if ((!actionIs0) && (!actionIs1) && (!actionIs2)
                && (!actionIs3) && (!actionIs4)) {
            return false;
        }
        return true;
    }

    public static void showState(int NumberOfPad, PadUnit[] padArray) {
        System.out.println("Rocket Pad Control Button system table");
        for (int j = 1; j <= NumberOfPad; j++) {
            println();
            ControlButtonState stateRocket1 = controller.map.get(padArray[j]).getState1();
            ControlButtonState stateRocket2 = controller.map.get(padArray[j]).getState2();
            System.out.println("Pad " + j + "Rocket 1: " + "Control Button State: " + stateRocket1);
            System.out.println("Pad " + j + "Rocket 2: " + "Control Button State: " + stateRocket2);
        }
    }

    public static Controller controller = new Controller();

    public static void main(String[] args) throws IOException {
        String rocketInfo = "";
        int MaxPad = 8;
        String action;
        terminateInstruction();
        println();
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        boolean notHaltProgram1 = true;
        boolean notHaltProgram2 = true;

        //number of pads that are going to be registered in the PadUnitManager
        int intNumOfPad = 9;

        //for each step this is the input, the padNumber, rocketNumber and rocketAction
        int padNumber = 1;
        int rocketNumber = 1;
        int rocketAction = 1;


        String inputPadName = "";
        boolean actionIsActivate = false;
        int result = 2;
        int controllerResult = 0;

        int stepCount = 0;


        while (stepCount <= 10) {
            int inputNumOfPad = 0;
            try {
                PadUnitManager padUnitManager = new PadUnitManager("8");//Checking input validity here
                result = makeStep(padUnitManager, rocketAction, intNumOfPad, padNumber, rocketNumber, false);
                ++stepCount;
            } catch (InvalidInputException e) {
                System.out.println(e);
            }

        }
        /*while (notHaltProgram1) {
            try {
                System.out.println("Enter number of pad (Maximum 8)");
                String inputNumOfPad = reader.readLine();
                boolean inputIs0 = inputNumOfPad.equals("0");
                if (inputIs0) {
                    notHaltProgram1 = false;
                }
                boolean createPadUnitManagerIfContinueProgram = true;
                if (notHaltProgram1 && createPadUnitManagerIfContinueProgram) {
                    PadUnitManager padUnitManager = new PadUnitManager(inputNumOfPad);//Checking input validity here
                    intNumOfPad = Integer.parseInt(inputNumOfPad);
                    while (notHaltProgram2 *//*&& notHaltProgram1*//*) {
                        try {
                            if (actionIsActivate == true) {
                                println();
                                System.out.println("Enter action for rocket " + rocketInfo +
                                        "(only 2('armed') and 4('reset') are available) (The system of this rocket will be reset in 10 seconds if no more action is executed.");
                                byte[] inputData = new byte[20];
                                //function readInputStreamWithTimeout and input0 will have problem if parameter for inputdata
                                //have more than 20 characters
                                String nextAction = readInputStreamWithTimeout(System.in, inputData, 10000, padUnitManager.padArray, inputPadName, rocketInfo);
                                boolean nextActionIsTimeout = nextAction.equals("Time out case");
                                boolean actionValid = actionValidity(nextAction);
                                if (nextActionIsTimeout == false) {
                                    if (actionValid == true) {
                                        int intNextAction = Integer.parseInt(nextAction);
                                        if (intNextAction == 0) {
                                            notHaltProgram2 = false;
                                            notHaltProgram1 = false;
                                        } else if (intNextAction == 1) {
                                            throw new InvalidInputException("Control Buttons are activated already");
                                        } else {
                                            controllerResult = controller.takeAction(intNumOfPad, padUnitManager.padArray, padNumber, rocketNumber, intNextAction, nextActionIsTimeout);
                                            ExceptionInputCase(controllerResult);
                                            println();
                                        }
                                    }
                                    if (actionValid == false) {
                                        throw new InvalidInputException("Action can only be 1('activate'), 2('armed'), 3('launch'), or 4('reset')");
                                    }
                                }
                                actionIsActivate = false;
                            } else {
                                println();
                                System.out.println("Input0: Enter pad name");
                                inputPadName = reader.readLine();
                                inputIs0 = inputPadName.equals("0");
                                if (inputIs0) {
                                    notHaltProgram2 = false;
                                    notHaltProgram1 = false;
                                } else {
                                    System.out.println("Input1: Enter rocket number (1 or 2)");
                                    rocketInfo = reader.readLine();
                                    inputIs0 = rocketInfo.equals("0");
                                    if (inputIs0) {
                                        notHaltProgram2 = false;
                                        notHaltProgram1 = false;
                                    }

                                    CheckPadNameAndRocketNumberThenInputRocketAction(rocketInfo, padUnitManager.padArray, inputPadName, inputNumOfPad);
                                    rocketNumber = Integer.parseInt(rocketInfo);
                                    padNumber = Integer.parseInt(inputPadName);
                                    action = reader.readLine();
                                    //actionResult = ;
                                    if (actionValidity(action)) {
                                        rocketAction = Integer.parseInt(action);
                                        boolean ActionIsTimeout = action.equals("Time out case");
                                        inputIs0 = (rocketAction == 0);
                                        if (inputIs0) {
                                            notHaltProgram2 = false;
                                            notHaltProgram1 = false;
                                        }
                                        if (notHaltProgram2) {

                                            result = makeStep(padUnitManager, rocketAction, intNumOfPad, padNumber, rocketNumber, ActionIsTimeout);
                                            if (result == 11)
                                            {
                                                actionIsActivate = true;
                                            }
                                            if (result == 1)
                                            {
                                                actionIsActivate = false;
                                            }
                                            ExceptionInputCase(result);
                                        }
                                    }
                                    else
                                    {
                                        throw new InvalidInputException("Action can only be 1('activate'), 2('armed'), 3('launch'), or 4('reset')");
                                    }
                                }
                            }
                            if (!inputIs0 && !actionIsActivate) {
                                showState(intNumOfPad, padUnitManager.padArray);
                            }
                        } catch (InvalidInputException e) {
                            System.out.println(e);

                        }
                        createPadUnitManagerIfContinueProgram = false;
                    }
                }
            } catch (InvalidInputException e) {
                System.out.println(e);
            }
        }*/
    }
}
