public class Voting {
    boolean out = false;

    public void vote1(boolean a, boolean b, boolean c) {
        out = (a && b) || (b && c) || (a && c);
    }

    public void vote2(boolean a, boolean b, boolean c, int threshold) {
        out = (a && b) || (b && c) || (a && c) && (threshold > 5);
    }

    public void vote3(boolean a, boolean b, boolean c) {
        out = a || b || c;
    }

    public static void main(String[] args){

    }
}
