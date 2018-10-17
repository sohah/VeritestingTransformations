public class TestVeritestingReplace extends TestVeritesting {


    void testHarness(TestRegionBaseClass v,
                     int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                     char c0, char c1, char c2, char c3, char c4, char c5) {
        Outputs outSPF = SPFWrapper(v, in0, in1, in2, in3, in4, in5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5);
        replace.reset();
        Outputs outJR = JRWrapper(v, in0, in1, in2, in3, in4, in5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5);
        checkEquality(v, outSPF, outJR);
    }
};
