//package Launch;

package AnRocketLaunch;

enum ControlButtonState {
    invalid, armedLaunchAvailable, launchAvailable, launched, inactive;
}

class ControlButton {
    Button ArmedButton1;
    Button LaunchButton1;
    Button ResetButton1;
    Button ArmedButton2;
    Button LaunchButton2;
    Button ResetButton2;

    public ControlButton() {
        this.ArmedButton1 = new Button();
        this.LaunchButton1 = new Button();
        this.ResetButton1 = new Button();
        this.ArmedButton2 = new Button();
        this.LaunchButton2 = new Button();
        this.ResetButton2 = new Button();
    }

    public void activateControlButton(int rocketName) {
        if (rocketName == 1) {
            ArmedButton1.activate();
            ResetButton1.activate();
        } else {
            ArmedButton2.activate();
            ResetButton2.activate();
        }
    }

    public void armedLaunchButtonPressed(PadUnit pad, int rocketName) {
        if (rocketName == 1) {
            LaunchButton1.activate();
            ArmedButton1.pressed();
            pad.rocket1.closeRelay1();
        } else {
            LaunchButton2.activate();
            ArmedButton2.pressed();
            pad.rocket2.closeRelay1();
        }
    }

    public void launchButtonPressed(PadUnit pad, int rocketName) {
        if (rocketName == 1) {
            LaunchButton1.pressed();
            pad.rocket1.closeRelay2();
        } else {
            LaunchButton2.pressed();
            pad.rocket2.closeRelay2();
        }
    }

    public void reset(PadUnit pad, int rocketName) {
        if (rocketName == 1) {
            ArmedButton1.reset();
            LaunchButton1.reset();
            pad.rocket1.resetRelays();
        } else {

            ArmedButton2.reset();
            LaunchButton2.reset();
            pad.rocket2.resetRelays();
        }
    }

    public ControlButtonState getState1() {
        if ((ArmedButton1.state() == ButtonState.inactive) &&
                (LaunchButton1.state() == ButtonState.inactive)) {
            return ControlButtonState.inactive;
        } else if ((ArmedButton1.state() == ButtonState.notPressed) &&
                (LaunchButton1.state() == ButtonState.inactive)) {
            return ControlButtonState.armedLaunchAvailable;
        } else if ((ArmedButton1.state() == ButtonState.pressed) &&
                (LaunchButton1.state() == ButtonState.notPressed)) {
            return ControlButtonState.launchAvailable;
        } else if ((ArmedButton1.state() == ButtonState.pressed) &&
                (LaunchButton1.state() == ButtonState.pressed)) {
            return ControlButtonState.launched;
        }
        return ControlButtonState.invalid;
    }

    public ControlButtonState getState2() {
        if ((ArmedButton2.state() == ButtonState.inactive) &&
                (LaunchButton2.state() == ButtonState.inactive)) {
            return ControlButtonState.inactive;
        } else if ((ArmedButton2.state() == ButtonState.notPressed) &&
                (LaunchButton2.state() == ButtonState.inactive)) {
            return ControlButtonState.armedLaunchAvailable;
        } else if ((ArmedButton2.state() == ButtonState.pressed) &&
                (LaunchButton2.state() == ButtonState.notPressed)) {
            return ControlButtonState.launchAvailable;
        } else if ((ArmedButton2.state() == ButtonState.pressed) &&
                (LaunchButton2.state() == ButtonState.pressed)) {
            return ControlButtonState.launched;
        }
        return ControlButtonState.invalid;
    }

    //}


}

