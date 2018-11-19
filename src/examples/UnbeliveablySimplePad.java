public class UnbeliveablySimplePad {
    private boolean startBtn;
    private boolean launchBtn;

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
    final int INVALIDSTATE = 5;


    public UnbeliveablySimplePad() {
        startBtn = false;
        launchBtn = false;
    }

    public static void main(String[] args) {
        UnbeliveablySimplePad pad = new UnbeliveablySimplePad();
        int s1 = 1;
        int s2 = 2;
        int s3 = 3;
        pad.runPadSteps(s1, s2, s3);
    }

    public void runPadSteps(int s1, int s2, int s3) {
        boolean ignition;
        runPad(s1);
        ignition = runPad(s2);
        if (ignition)
            launchRocket();
    }

    private void launchRocket() {
        System.out.println("Rocket launched successfully.");
        startBtn = false;
        launchBtn = false;
    }

    /**
     * It takes the input signal n, which either can be start, launch or empty, it has no reset. So basically, it must go fom "IDLE" to
     * "READY" to "LAUNCH", but it might stay indefinitely in any of the first two states. While it can only stay in the "LAUNCH" state for only one time slot.
     * @param n
     * @return
     */
    public boolean runPad(int n) {
        boolean startSignal;
        boolean launchSignal;
        boolean emptySignal;

        startSignal = (n == 1);
        launchSignal = (n == 2);
        emptySignal = (!startSignal && !launchSignal);
        int currentState = getCurrentState();

        boolean ignitionSignal = false;
        if (!emptySignal) { //only proceed if a non-empty signal was received.
            if (currentState == IDLE) { // this condition is unbounded by time, so it is not part of the switch statement below.
                if (startSignal) {
                    startBtn = true;
                }
            } else { // !(currentState == PadState.IDLE)  && (!emptySignal)
                if (currentState == READY) {
                    if (launchSignal) {
                        launchBtn = true;
                        ignitionSignal = true;
                    }
                }
            }
        }
        return ignitionSignal;
    }

    public int getCurrentState() {
        int padState;
        if (!startBtn && !launchBtn) //Start State
            padState = IDLE;
        else if (startBtn && !launchBtn) //Ready State
            padState = READY;
        else if (!startBtn && launchBtn) // Launch State
            padState = LAUNCH;
        else
            padState = INVALIDSTATE; // Invalid State
        return padState;
    }
}
