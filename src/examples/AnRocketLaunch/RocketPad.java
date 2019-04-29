//package Launch;

package AnRocketLaunch;

class RocketPad
    //true: rocket1; false: rocket2
{
    //Variable
    private int rocketName;
    private Button activateButton; // This thing will be observed
    private boolean relay1;
    private boolean relay2;
    //--------------------------------------------------------------------

    public RocketPad(int rocketName) //Constructor
    {
        activateButton = new Button();
        relay1 = false;//open
        relay2 = false;//open
        this.rocketName = rocketName;
    }
    //Open: False; Close: True
    //Enum State;//Active, inactive
    public void activateButtonPressed(PadUnit pad) throws InvalidInputException
    {
        //Send signal to PadUnit
        activateButton.activate();
        AnMainSymbolic.controller.activateControlButton(pad,rocketName);//throw InvalidInputException here
    }

    void getRelayState()
    {
        System.out.println("Rocket: " + rocketName);
        System.out.println("relay1: "+relay1);
        System.out.println("relay2: " + relay2);
    }
    void closeRelay1()
    {
        relay1 = true;
    }

    void closeRelay2()
    {
        relay2 = true;
    }

    void resetRelays()
    {
        relay1 = false;
        relay2 = false;
        activateButton.reset();
    }

}
