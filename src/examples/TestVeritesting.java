public class TestVeritesting {


    void testHarness(TestRegionBaseClass v, int in0) {
        int outSPF = SPFWrapper(v, in0);
        int outJR = JRWrapper(v, in0);
        checkEquality(v, outSPF, outJR);
    }

    private void checkEquality(TestRegionBaseClass v, int outSPF, int outJR) {
//        if (outSPF == outJR) System.out.println("Match");
//        else System.out.println("Mismatch");
        assert(outSPF == outJR);
    }

    private int SPFWrapper(TestRegionBaseClass v, int in0) {
        return NoVeritest(v, in0);
    }

    private int NoVeritest(TestRegionBaseClass v, int in0){ return SPFWrapperInner(v, in0); }

    private int SPFWrapperInner(TestRegionBaseClass v, int in0) {
        int ret = v.testFunction(in0);
        return ret;
    }

    private int JRWrapper(TestRegionBaseClass v, int in0) { return v.testFunction(in0); }

    public void runTests() {
        testHarness(new Simple1(), 1);
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        t.runTests();
    }

};
