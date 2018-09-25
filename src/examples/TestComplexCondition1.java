public class TestComplexCondition1 extends TestRegionBaseClass {

    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return mwwTestComplexCondition1(b0, b1, b2, b3, in0);
    }

    public static Outputs mwwTestComplexCondition1(boolean w, boolean x, boolean y, boolean z, int a) {
        if ((w && x) || (y && z)) {
            a = a + 1;
        } else {
            a = a * 2;
        }
        Outputs o = new Outputs();
        o.intOutputs = new int[1];
        o.intOutputs[0] = a;
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        TestComplexCondition1 s = new TestComplexCondition1();
        t.runTest(s);
    }
}

