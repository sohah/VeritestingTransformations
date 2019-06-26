public class EvenImplementation {
    int countState = 0;

    public static void main(String[] args) {
        EvenImplementation evenImpl = new EvenImplementation();
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
