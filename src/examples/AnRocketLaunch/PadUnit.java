//package Launch;
package AnRocketLaunch;

class PadUnit
{
    RocketPad rocket1= new RocketPad(1);
    RocketPad rocket2 = new RocketPad(2);
    public int name;
    public PadUnit(int name) //Constructor
    {
        AnMainSymbolic.controller.registerPad(this);
        this.name = name;
    }

    public void activateButtonRocketPressed(int rocketName) throws InvalidInputException
    {
        //Send signal to controller

        if (rocketName == 1)
        {
            rocket1.activateButtonPressed(this);
        }
        else
        {
            rocket2.activateButtonPressed(this);
        }

    }

}
