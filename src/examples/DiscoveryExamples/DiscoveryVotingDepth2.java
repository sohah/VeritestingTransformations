package DiscoveryExamples;

public class DiscoveryVotingDepth2 {
    boolean out = false;

    public void vote(boolean a, boolean b, boolean c) {
        out = a || b || c;
    }

    public void vote0(boolean a, boolean b, boolean c) {
        out = a;
    }

    public static void main(String[] args) {
        DiscoveryVotingDepth2 discoveryVoting = new DiscoveryVotingDepth2();
        discoveryVoting.makeStep(true, true, true, 4, false, true);
    }


    public void makeStep(boolean a, boolean b, boolean c, int threshold, boolean out, boolean symVar) {
        this.out = out;

        if (symVar)
            vote(a, b, c);
    }
}
