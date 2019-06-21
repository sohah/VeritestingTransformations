public class EvenImplementation {
    int countState = 0;

    public static void main(String[] args) {


        EvenImplementation evenImpl = new EvenImplementation();
        boolean signal = false;
        evenImpl.makeStep(signal, true);
    }

    private void makeStep(boolean signal, boolean symVar) {
        int output = 0;

        if (symVar)
            output = run(signal);

        System.out.println("output value = " + output);
    }

    private int run(boolean signal) {
        if (signal)
            ++this.countState;
        if (countState % 2 == 0)
            return 7;
        else
            return 20;
    }

}
