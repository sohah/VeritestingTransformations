public class Voting {
    boolean out = false;

    public void vote1(boolean a, boolean b, boolean c) {
        out = (a && b) || (b && c) || (a && c);
    }

    public void vote2(boolean a, boolean b, boolean c, int threshold) {
        out = ((a && b) || (b && c) || (a && c)) && (threshold < 10) && (threshold > 5);
    }

    public void vote3(boolean a, boolean b, boolean c) {
        out = a || b || c;
    }

    public void vote0(boolean a, boolean b, boolean c) {
        out = a;
    }

    public static void main(String[] args) {
        Voting voting = new Voting();
        voting.makeStep(true, true, true, 4, false, true);
    }


    public void makeStep(boolean a, boolean b, boolean c, int threshold, boolean out, boolean symVar) {
        this.out = out;

        if (symVar)
            vote0(a, b, c);
    }
}
