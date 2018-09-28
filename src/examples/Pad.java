import java.util.Scanner;

/**
 * Safety Properties:
 * 1. G_b (! pad.INVALIDSTATE), Safety property that describes the fact that in a bounded time that the pad will never be in an INVALID state.
 * 2. G_b0 (startSignal -> E_b1 armSignal -> E_b1 launchSignal -> E_b2 ignitionSignal), Verify through the model in a bounded time b0, that if a startSignal is followed by a launchSignal will always result in a ignitionSignal in bounded time b2.
 */

public class Pad {
    private boolean startBtn;
    private boolean armBtn;
    private boolean launchBtn;
    private long stateChangeDuration; // expresses the time when a state has changed.

    enum PadState {
        IDLE,
        READY,
        ARM,
        LAUNCH,
        RESET,
        INVALIDSTATE
    }

    public Pad() {
        startBtn = false;
        armBtn = false;
        launchBtn = false;
    }

    public static void main(String[] args) throws Exception {
        Pad pad1 = new Pad();
        Scanner reader = new Scanner(System.in);
        boolean startSignal, armSignal, launchSignal, emptySignal;
        long currentTime;

        while (true) {
            //for every tick runPad should be called, this should be implemented through a thread.
            System.out.println("Enter a signal number (0-emptySignal) (1-startSignal) (2-armSignal) (3-launchSignal): ");
            int n = reader.nextInt();

            emptySignal = (n == 0 ? true : false);
            startSignal = (n == 1 ? true : false);
            armSignal = (n == 2 ? true : false);
            launchSignal = (n == 3 ? true : false);

            currentTime = System.nanoTime();

            System.out.println("Before Transition");
            pad1.printCurrentState();
            pad1.printSignal(n);
            boolean ignition = (pad1).runPad(startSignal, armSignal, launchSignal, emptySignal); // this needs to be in a thread
            System.out.println("After Transition");
            pad1.printCurrentState();

            if (ignition)
                pad1.launchRocket();
        }
    }

    private void launchRocket() {
        System.out.println("Rocket launched successfully.");
        this.startBtn = false;
        this.armBtn = false;
        this.launchBtn = false;
        this.stateChangeDuration = 0;
    }

    private Boolean runPad(boolean startSignal, boolean armSignal, boolean launchSignal, boolean emptySignal) throws Exception {
        boolean ignitionSignal = false;
        if (!emptySignal) //only proceed if a non-empty signal was received.
            if (getCurrentState() == PadState.IDLE) { // this condition is unbounded by time, so it is not part of the switch statement below.
                if (startSignal && !armSignal && !launchSignal) {
                    this.startBtn = true;
                } else //unexpected input then reset
                    this.startBtn = false;
                this.armBtn = false;
                this.launchBtn = false;
                ++this.stateChangeDuration;
            } else {
                switch (getCurrentState()) {
                    case READY:
                        if (!startSignal && armSignal && !launchSignal) {
                            this.armBtn = true;
                        } else //unexpected input then reset
                            this.armBtn = false;
                        this.startBtn = false;
                        this.launchBtn = false;
                        ++this.stateChangeDuration;
                        break;
                    case ARM:
                        if (!startSignal && !armSignal && launchSignal) {
                            this.launchBtn = true;
                        } else //unexpected input then reset
                            this.launchBtn = false;
                        this.startBtn = false;
                        this.launchBtn = false;
                        ignitionSignal = true;
                        ++this.stateChangeDuration;
                        break;
                    case LAUNCH:
                        throw new Exception("Exception raised! lauch state is detected after ignition");
                    case RESET: // grace time passed, needs reset.
                        startBtn = false;
                        armBtn = false;
                        launchBtn = false;
                        this.stateChangeDuration = 0;
                        break;
                }
            }
            else{
                ++this.stateChangeDuration;
                if(getCurrentState() == PadState.RESET){
                    startBtn = false;
                    armBtn = false;
                    launchBtn = false;
                    this.stateChangeDuration = 0;
                }
        }
        return ignitionSignal;
    }

    public PadState getCurrentState() {
        PadState padState;
        if (!startBtn && !armBtn && !launchBtn) //Start State
            padState = PadState.IDLE;
        else if (startBtn && !armBtn && !launchBtn && inValidPeriod()) //Ready State
            padState = PadState.READY;
        else if (!startBtn && armBtn && !launchBtn && inValidPeriod()) //Arm State
            padState = PadState.ARM;
        else if (!startBtn && !armBtn && launchBtn && inValidPeriod()) // Launch State
            padState = PadState.LAUNCH;
        else if (!inValidPeriod()) // Reset State
            padState = PadState.RESET;
        else
            padState = PadState.INVALIDSTATE; // Invalid State
        return padState;
    }

    /**
     * Defines a valid period that is at most 15 seconds from the last state change.
     */
    private boolean inValidPeriod() {
        return (this.stateChangeDuration > 5) ? false : true;
    }

    private void printCurrentState(){
        switch (getCurrentState()) {
            case IDLE:
                System.out.println("Pad is in IDLE state");
                break;
            case READY:
                System.out.println("Pad is in READY state");
                break;
            case ARM:
                System.out.println("Pad is in ARM state");
                break;
            case LAUNCH:
                System.out.println("Pad is in LAUNCH state");
                break;
            case RESET:
                System.out.println("Pad is in RESET state");
                break;
            case INVALIDSTATE:
                System.out.println("Pad is in INVALID state");
                break;
        }
    }

    private void printSignal(int signal){
        String s;
        s = (signal == 0? "EMPTY Signal": ((signal == 1)? "START Signal" : (signal == 2)? "ARAM Signal": (signal == 3)? "LAUNCH Signal": "Wrong Signal"));
        System.out.println(" Received:  " +s);
    }
}
