package DiscoveryExamples;

public class Voting {
    boolean out = false;

    public void vote1(boolean a, boolean b, boolean c) {
        out = (a && b) || (b && c) || (a && c);
    }

    public void vote2(boolean a, boolean b, boolean c, int threshold) {
        out = ((a && b) || (b && c) || (a && c)) && (threshold < 10) && (threshold > 5);
    }

    public static void main(String[] args) {
        Voting discoveryVoting = new Voting();
        discoveryVoting.makeStep(true, true, true, 4, false, true);
    }


    public void makeStep(boolean a, boolean b, boolean c, int threshold, boolean out, boolean symVar) {
        this.out = out;

        vote2(a, b, c, threshold);
        assert this.out ? ((b && a) || (b ^ a)) : true;

    }
}
