package AnRocketLaunch;

class PadUnitManager {
    public static PadUnit[] padArray = new PadUnit[9];

    public boolean numberOfPadValidity(String numOfPad) throws InvalidInputException {

        for (int k = 0; k <= 8; k++) {//may be null pointer is here. k can start from 0 to fix the problem
            String intToStringk = Integer.toString(k);
            if (numOfPad.equals(intToStringk)) {
                return true;
            }
        }
        return false;
    }

    public PadUnitManager(String inputNumberOfPads) throws InvalidInputException// Constructor
    {
        int NumberOfPad = Integer.parseInt(inputNumberOfPads);
        String padRegisterSuccessful = NumberOfPad + " pads are registered successfully";
        boolean runWhileLoopOnce1 = true;

        while ((numberOfPadValidity(inputNumberOfPads) == false) && runWhileLoopOnce1) {
            runWhileLoopOnce1 = false;
            throw new InvalidInputException("Invalid number of pads");
        }
        boolean runWhileLoopOnce2 = true;
        while (runWhileLoopOnce1 == true && runWhileLoopOnce2) {
            //PadUnit[] padArray = new PadUnit[NumberOfPad + 1];// create array of PadUnit
            System.out.println(padRegisterSuccessful);

            for (int i = 1; i < (NumberOfPad + 1); i++) {
                padArray[i] = new PadUnit(i); //Create instance of PadUnit
                //Only show Pad from 1

                System.out.println("Pad" + i + ": on");

            }
            runWhileLoopOnce2 = false;
        }
    }

    public int takeAction(int inputNumOfPad, int inputPadName, int rocketName) {
        try {
            padArray[inputPadName].activateButtonRocketPressed(rocketName);
            return 1;
        } catch (InvalidInputException e) {
            return 7;
        }


    }
}
