public class UnbeliveablySimplePad {
    private boolean start_btn;
    private boolean launch_btn;
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
        start_btn = false;
        launch_btn = false;
    }

    public static void main(String[] args) {
        UnbeliveablySimplePad pad = new UnbeliveablySimplePad();
        int count = 1;
        boolean start_btn = false;
        boolean launch_btn = false;
        boolean ignition = false;
        int sig = 1;

        pad.runPadSteps(sig, start_btn, launch_btn, ignition, true);

    }

    public void runPadSteps(int sig, boolean start_btn, boolean launch_btn, boolean ignition, boolean symVar) {

        //make pad state symbolic.
        this.start_btn = start_btn;
        this.launch_btn = launch_btn;
        this.ignition = ignition;

        boolean rocketLaunched = false;
        //Scanner reader = new Scanner(System.in);

        //while (true) {
            //System.out.println("Enter a signal number (0-emptySignal) (1-startSignal) (2-armSignal) (3-launchSignal): ");
            //int n = reader.nextInt();

            if (symVar) { // used to make this a veritesting region
                rocketLaunched = runPad(sig); //running it here one step, but should be enclosed in a loop in real program.
                //assert (rocketLaunched ? getState() == IGNITION : true);
            }
            if (rocketLaunched) {
                // resetPad(); this is another variant of resetting the pad, for now let's reset the pad in the next step.
                System.out.println("Rocket launched successfully.");
            } else
                System.out.println("Rocket still not launched.");
            //     }
        //}
    }

    private void resetPad() {
        start_btn = false;
        launch_btn = false;
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
            boolean startOrLaunch;

            startSignal = (n == 0);
            launchSignal = (n == 1);
            startOrLaunch = startSignal || launchSignal; //we have a problem in summarizing complex conditions

            if (startOrLaunch) { //only proceed if a non-empty signal was received, otherwise remain in the same state, ignoring incoming signal
                if (perivousState == IDLE) {
                    if (startSignal) {
                        start_btn = true;
                    }
                } else {
                    if (perivousState == READY) {
                        if (launchSignal) {
                            launch_btn = true;
                        }
                    }
                }
            }
        }
        return ignition;
    }

    public int getState() {
        int padState;
        boolean mystartBtn = this.start_btn;
        boolean myLaunchBtn = this.launch_btn;
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
