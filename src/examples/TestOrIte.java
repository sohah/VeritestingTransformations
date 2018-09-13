public class TestOrIte extends TestRegionBaseClass {

    int testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return mwwTestOrIte(b0, b1, in0);
    }

    public static int mwwTestOrIte(boolean x, boolean y, int a) {
        if (x || y) {
            a = a + 1;
        } else {
            a = a - 1;
        }
        return a;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestOrIte s = new TestOrIte();
        t.runTest(s);
    }
}

