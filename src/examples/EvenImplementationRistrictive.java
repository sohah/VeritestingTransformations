public class EvenImplementationRistrictive {
    int countState = 0;
    int output = 0;


    public static void main(String[] args) {
        EvenImplementationRistrictive evenImpl = new EvenImplementationRistrictive();
        boolean signal = false;
        evenImpl.makeStep(signal, 1, 1, true);
    }

    private void makeStep(boolean signal, int countState, int output, boolean symVar) {
        this.countState = countState;
        this.output = output;

        if (symVar)
            output = runEven(signal);

        System.out.println("output value = " + output);
    }

    private int runEven(boolean signal) {
        if (signal)
            ++this.countState;
        if (countState % 2 == 0)
            output = computeOutput();
        else
            output = computeOutput();

        return output;
    }

    //constraints the output to be from 1 to 9 and excluding the number 9.
    private int computeOutput() {
        ++output;
        if (output == 5)
            ++output;

        if (output == 10)
            output = 0;

        return output;
    }

}
