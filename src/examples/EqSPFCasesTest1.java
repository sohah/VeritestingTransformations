public class EqSPFCasesTest1 extends TestRegionBaseClass {

    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                         boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return createObjectTC8(b0, b1);
    }

    int count = 0;

    public Outputs createObjectTC8(boolean x, boolean y) {
        int a = 0;
        if (x) {
            a = 3 + a;
        } else {
            a = 2 + a;
            TempClass tempClass2 = new TempClass();
        }

        if (y) {
            a = 4 + a;
        } else {
            a = 2 + a;
        }
      Outputs o = new Outputs();
        o.intOutputs = new int[a];
        return o;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        EqSPFCasesTest1 s = new EqSPFCasesTest1();
        t.runTest(s);
    }
}
