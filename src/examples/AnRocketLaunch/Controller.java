
package AnRocketLaunch;


import java.util.HashMap;

class Controller {
    HashMap<PadUnit, ControlButton> map = new HashMap<>();

    public Controller() {
    }

    /*
    boolean rocketNameIs1 = rocketInfo.equals("1");// to pass to controller.Acion
                                        boolean actionIs2 = nextAction.equals("2");
                                        boolean actionIs3 = nextAction.equals("3");
                                        boolean actionIs4 = nextAction.equals("4");
     */
    public void takeAction(int inputNumOfPad, PadUnit[] pad,int padNumber, int rocketName, int action, boolean actionIsTimeout) throws InvalidInputException {
        // takeAction check for input so argiments has to be String
        if (!actionIsTimeout) {
            {
                if (rocketName == 1) {
                    if (action == 2) {
                        armedLaunchButtonPressed(pad[padNumber], 1);
                    } else if (action == 3) {
                        launchButtonPressed(pad[padNumber], 1);
                    } else if (action == 4) {
                        reset(pad[padNumber], 1);
                    }
                    pad[padNumber].rocket1.getRelayState();
                } else {
                    if (action == 2) {
                        armedLaunchButtonPressed(pad[padNumber], 2);
                    } else if (action == 3) {
                        launchButtonPressed(pad[padNumber], 2);
                    } else if (action == 4) {
                        reset(pad[padNumber], 2);
                    }
                    pad[padNumber].rocket2.getRelayState();
                }
            }
        }
    }
    public void registerPad(PadUnit pad) {
        ControlButton controlButton = new ControlButton();
        //Create control button for Pad
        map.put(pad, controlButton);
    }

    public void deregisterPad(PadUnit pad) {
        map.remove(pad);
    }

    public void activateControlButton(PadUnit pad, int rocketName) throws InvalidInputException {
        if (rocketName == 1) {
            ControlButtonState state = map.get(pad).getState1();
            //check state
            if (state == ControlButtonState.inactive) {
                map.get(pad).activateControlButton(rocketName);
                //System.out.println("Control Button Activated");
                state = map.get(pad).getState1();//update state
                System.out.println("Control Buttons were activated");
                //System.out.println("Pad " + pad.name + ": Rocket " + rocketName + "- Current Control Button state: " + state);
            } else if (state == ControlButtonState.armedLaunchAvailable) {
                throw new InvalidInputException("Control Buttons are activated already");
            } else if (state == ControlButtonState.launchAvailable) {
                throw new InvalidInputException("Control Buttons are activated already");
            } else if (state == ControlButtonState.launched) {
                throw new InvalidInputException("Mission done already! Nothing more to press");
            }
        } else {
            ControlButtonState state = map.get(pad).getState2();
            //check state
            if (state == ControlButtonState.inactive) {
                map.get(pad).activateControlButton(rocketName);
                //System.out.println("Control Button Activated");
                state = map.get(pad).getState2();//update state
                //System.out.println("Pad " + pad.name + ": Rocket " + rocketName + "- Current Control Button state: " + state);
            } else if (state == ControlButtonState.armedLaunchAvailable) {
                throw new InvalidInputException("Control Buttons are activated already");
            } else if (state == ControlButtonState.launchAvailable) {
                throw new InvalidInputException("Control Buttons are activated already");
            } else if (state == ControlButtonState.launched) {
                throw new InvalidInputException("Mission done already! Nothing more to press");
            }
        }

    }

    public void reset(PadUnit pad, int name) {
        map.get(pad).reset(pad, name);
        System.out.println("reset done");
        if (name == 1) {
            ControlButtonState state = map.get(pad).getState1();//update state
            //System.out.println("Pad " + pad.name + ": Rocket " + name + "- Current Control Button state: " + state);
        } else {
            ControlButtonState state = map.get(pad).getState2();//update state
            //System.out.println("Pad " + pad.name + ": Rocket " + name + "- Current Control Button state: " + state);
        }
    }

    public void armedLaunchButtonPressed(PadUnit pad, int rocketName) throws InvalidInputException {
        if (rocketName == 1) {
            ControlButtonState state = map.get(pad).getState1();
            //check state
            if (state == ControlButtonState.inactive) {
                throw new InvalidInputException("armed button is unavaiable now");
            } else if (state == ControlButtonState.armedLaunchAvailable) {
                map.get(pad).armedLaunchButtonPressed(pad, rocketName);
                System.out.println("armed pressed");
                state = map.get(pad).getState1();//update state
                //System.out.println("Pad " + pad.name + ": Rocket " + rocketName + "- Current Control Button state: " + state);
            } else if (state == ControlButtonState.launchAvailable) {
                reset(pad, rocketName);
            } else if (state == ControlButtonState.launched) //this condition will never executed
            {
                throw new InvalidInputException("Mission done already! Nothing more to press!");
            }
        } else //2
        {
            ControlButtonState state = map.get(pad).getState2();
            //check state
            if (state == ControlButtonState.inactive) {
                throw new InvalidInputException("Buttons unavaiable now");
            } else if (state == ControlButtonState.armedLaunchAvailable) {
                map.get(pad).armedLaunchButtonPressed(pad, rocketName);
                System.out.println("armed pressed");
                state = map.get(pad).getState2();//update state
                //System.out.println("Pad " + pad.name + ": Rocket " + rocketName + "- Current Control Button state: " + state);
            } else if (state == ControlButtonState.launchAvailable) {
                reset(pad, rocketName);
            } else if (state == ControlButtonState.launched) {
                throw new InvalidInputException("Mission done already! Nothing more to press!");
            }

        }
    }

    public void launchButtonPressed(PadUnit pad, int rocketName) throws InvalidInputException {
        String launchSuccess = ("Rocket " + rocketName + ": Launch!!!!!");
        if (rocketName == 1) {
            ControlButtonState state = map.get(pad).getState1();
            //check state
            if (state == ControlButtonState.inactive) {
                throw new InvalidInputException("Launch button is inactive unavaiable now");
            } else if (state == ControlButtonState.armedLaunchAvailable) {
                throw new InvalidInputException("Launch button is inactive unavaiable now");
            } else if (state == ControlButtonState.launchAvailable) {
                map.get(pad).launchButtonPressed(pad, rocketName);
                System.out.println("Launch!!!!!");
                reset(pad, rocketName);
                state = map.get(pad).getState1();//update state
                //System.out.println("Pad " + pad.name + ": Rocket " + rocketName + "- Current Control Button state: " + state);
            } else if (state == ControlButtonState.launched)//This case will never be reached
            {
                throw new InvalidInputException("Mission done already! Nothing more to press");
            }
        } else {
            ControlButtonState state = map.get(pad).getState2();
            //check state
            if (state == ControlButtonState.inactive) {
                throw new InvalidInputException("Launch button is inactive unavaiable now");
            } else if (state == ControlButtonState.armedLaunchAvailable) {
                throw new InvalidInputException("Launch button is inactive unavaiable now");
            } else if (state == ControlButtonState.launchAvailable) {
                map.get(pad).launchButtonPressed(pad, rocketName);
                System.out.println(launchSuccess);
                reset(pad, rocketName);
                state = map.get(pad).getState2();//update state
                //System.out.println("Pad " + pad.name + ": Rocket " + rocketName + "- Current Control Button state: " + state);
            } else if (state == ControlButtonState.launched) {
                throw new InvalidInputException("Mission done already! Nothing more to press");
            }

        }

    }
}
/*if (actionValidity(action) == false) {// Valid action?
            throw new InvalidInputException("Action can only be 1('activate'), 2('armed'), 3('launch'), or 4('reset')");
        } else {
            int padNumber = Integer.parseInt(padName);
            boolean rocketNameIs1 = rocketName.equals("1");
            boolean solveIf1 = true;
            while (rocketNameIs1 && solveIf1) {
                if (action.equals("2")) {
                    armedLaunchButtonPressed(pad[padNumber], 1);
                } else if (action.equals("3")) {
                    launchButtonPressed(pad[padNumber], 1);
                } else if (action.equals("4")) {
                    reset(pad[padNumber], 1);
                }
                pad[padNumber].rocket1.getRelayState();
                solveIf1 = false;
            }
            boolean solveElse1 = true;
            while (solveIf1 == true && solveElse1) // rocketName = 2
            {
                boolean armedLaunchAction = action.equals("2");
                boolean launchAction = action.equals("3");
                boolean resetAction = action.equals("4");
                if (armedLaunchAction) {
                    armedLaunchButtonPressed(pad[padNumber], 2);
                } else if (launchAction) {
                    launchButtonPressed(pad[padNumber], 2);
                } else if (resetAction) {
                    reset(pad[padNumber], 2);
                }
                //pad[padNumber].rocket2.getRelayState();
                solveElse1 = false;
            }
        }*/