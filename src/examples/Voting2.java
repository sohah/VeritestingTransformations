public class Voting2 {
    boolean out = false;

    public void vote2(int a, int b, int c, int threshold) {
        out = false;

        if(a>2)
            if(b<(a+40))
                if(threshold < (a+b)+10)
                    if(threshold > (b+c -5))
                        out = true;
        if(b>10)
            if(c>(b+10))
                if(threshold < (a+b)+10)
                    if(threshold > (b+c -5))
                        out = true;

        if(a>0)
            if(c>0)
                if(threshold < (a+b)+10)
                    if(threshold > (b+c -5))
                        out = true;
    }

    public static void main(String[] args) {
        Voting2 voting = new Voting2();
        voting.makeStep(1, 1, 1, 4, false, true);
    }


    public void makeStep(int a, int b, int c, int threshold, boolean out, boolean symVar) {
        this.out = out;

        if (symVar)
            vote2(a, b, c, threshold);
    }
}
