public class TestNestedIfBranch extends TestRegionBaseClass {

    int testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return mwwNestedIfBranch(in0, in1);
    }

    public static int mwwNestedIfBranch(int x, int y) {
        if (x < y) {
            if (y < 100) {
                y = 100;
            } else {
                y = y * 2;
            }
        } else {
            y = x;
        }
        return y;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestNestedIfBranch s = new TestNestedIfBranch();
        t.runTest(s);
    }
}
