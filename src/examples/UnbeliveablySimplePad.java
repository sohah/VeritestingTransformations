public class UnbeliveablySimplePad {
    private boolean startBtn;
    private boolean launchBtn;
    private boolean ignition;

    /*enum PadState {
        IDLE,
        READY,
        LAUNCH,
        RESET,
        INVALIDSTATE
    }
*/

    final int IDLE = 1;
    final int READY = 2;
    final int LAUNCH = 3;
    final int IGNITION = 4;
    final int INVALIDSTATE = 5;


    public UnbeliveablySimplePad() {
        startBtn = false;
        launchBtn = false;
    }

    public static void main(String[] args) {
        UnbeliveablySimplePad pad = new UnbeliveablySimplePad();
        int n = 1;
        boolean startBtn = false;
        boolean launchBtn = false;
        boolean ignition = false;

        pad.runPadSteps(n, startBtn, launchBtn, ignition);

    }

    public void runPadSteps(int n, boolean startBtn, boolean launchBtn, boolean ignition) {

        //make pad state symbolic.
        this.startBtn = startBtn;
        this.launchBtn = launchBtn;
        this.ignition = ignition;

        boolean rocketLaunched = false;

        if (n < 6) {
     //       for (int i = 0; i < n; i++) {
                //if (symVar) { // used to make this a veritesting region
                    rocketLaunched = runPad(n); //running it here one step, but should be enclosed in a loop in real program.
                    //assert (rocketLaunched ? getState() == IGNITION : true);

                //}

             /*       if (rocketLaunched) {
                        // resetPad(); this is another variant of resetting the pad, for now let's reset the pad in the next step.
                        System.out.println("Rocket launched successfully.");
                    } else
                        System.out.println("Rocket still not launched.");*/
       //     }
        }
    }

    private void resetPad() {
        startBtn = false;
        launchBtn = false;
        ignition = false;
    }

    /**
     * It takes the input signal n, which either can be start, launch or empty, it has no reset. So basically, it must go fom "IDLE" to
     * "READY" to "LAUNCH", but it might stay indefinitely in any of the first two states. While it can only stay in the "LAUNCH" state for only one time slot.
     *
     * @param n
     * @return
     */
    public boolean runPad(int n) {
        int perivousState = getState();

        if (perivousState == LAUNCH) { //state needs to change regardless of the signal.
            ignition = true;
        } else if (perivousState == IGNITION || perivousState == INVALIDSTATE) { //state needs to change regardless of the signal.
            resetPad();
        } else {
            boolean startSignal;
            boolean launchSignal;
            boolean emptySignal;
            boolean startOrLaunch;

            startSignal = (n == 1);
            launchSignal = (n == 2);
            startOrLaunch = startSignal || launchSignal; //we have a problem in summarizing complex conditions

            //emptySignal = (!startSignal && !launchSignal);

            if (startOrLaunch) { //only proceed if a non-empty signal was received, otherwise remain in the same state, ignoring incoming signal
                if (perivousState == IDLE) {
                    if (startSignal) {
                        startBtn = true;
                    }
                } else {
                    if (perivousState == READY) {
                        if (launchSignal) {
                            launchBtn = true;
                        }
                    }
                }
            }
        }
        return ignition;
    }

    public int getState() {
        int padState;
        boolean mystartBtn = this.startBtn;
        boolean myLaunchBtn = this.launchBtn;
        boolean myIgnition = this.ignition;

        if (!mystartBtn && !myLaunchBtn && !myIgnition) //IDLE State
            padState = IDLE;
        else if (mystartBtn && !myLaunchBtn && !myIgnition) //Ready State
            padState = READY;
        else if (mystartBtn && myLaunchBtn && !myIgnition) // Launch State
            padState = LAUNCH;
        else if (mystartBtn && myLaunchBtn && myIgnition)
            padState = IGNITION;
        else
            padState = INVALIDSTATE; // Invalid State
        return padState;
    }

}
