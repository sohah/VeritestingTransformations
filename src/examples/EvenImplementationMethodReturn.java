/**
 * This class is exactly like the EvenImplementation class, except that its output is sent without being stored
 * as a state variable. The problem in having that is that, it becomes hard to define the initial state of the two
 * nodes on the output. The problem comes from the fact that the specification has the first step to initialize
 * where as this does not correspond to anything in the implementation. Our initial idea is to artificially add this
 * step into the implementation such that there is a corresponding value for the initialization step. While this approach
 * works for the pad for example, it does not work for this class because really the initial value of the output of the
 * method is undefined. Therefore somehow we need to make our assumptions and checking from the actual step instead of
 * the first initial step.
 */
public class EvenImplementationMethodReturn {
    int countState = 0;

    public static void main(String[] args) {
        EvenImplementationMethodReturn evenImpl = new EvenImplementationMethodReturn();
        boolean signal = false;
        evenImpl.makeStep(signal, 1,true);
    }

    private void makeStep(boolean signal, int countState, boolean symVar) {
        int output = 0;
        this.countState = countState;

        if (symVar)
            output = runEven(signal);

        System.out.println("output value = " + output);
    }

    private int runEven(boolean signal) {
        if (signal)
            ++this.countState;
        if (countState % 2 == 0)
            return 7;
        else
            return 20;
    }

}
