public class TestComplexCondition1 extends TestRegionBaseClass {

    int testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
//        return mwwTestComplexCondition1(b0, b1, b2, b3, in0);
        return mwwTestComplexCondition1(b0, b1, b2, b3);
    }

//    public static int mwwTestComplexCondition1(boolean w, boolean x, boolean y, boolean z, int a) {
    public static int mwwTestComplexCondition1(boolean w, boolean x, boolean y, boolean z) {
        int a = 0;
        if ((w && x) || (y && z)) {
            a = a + 1;
        } else {
            a = a * 2;
        }
        return a;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestComplexCondition1 s = new TestComplexCondition1();
        t.runTest(s);
    }
}

