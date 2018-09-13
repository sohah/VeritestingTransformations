public class TestVeritesting {


    void testHarness(TestRegionBaseClass v, int in0) {
        int outSPF = SPFWrapper(v, in0);
        int outJR = JRWrapper(v, in0);
        checkEquality(v, outSPF, outJR);
    }

    private void checkEquality(TestRegionBaseClass v, int outSPF, int outJR) {
        if (outSPF == outJR) System.out.println("Match");
        else {
            System.out.println("Mismatch");
            assert(false);
        }
//        assert(outSPF == outJR);
    }

    private int SPFWrapper(TestRegionBaseClass v, int in0) {
        return NoVeritest(v, in0);
    }

    // This is a special method. Call this method to prevent SPF from veritesting any regions that appear in any
    // function or method call higher up in the stack. In the future, this call to SPFWrapperInner can be changed to
    // be a generic method call if other no-veritesting methods need to be invoked.
    private int NoVeritest(TestRegionBaseClass v, int in0){ return SPFWrapperInner(v, in0); }

    private int SPFWrapperInner(TestRegionBaseClass v, int in0) {
        int ret = v.testFunction(in0);
        return ret;
    }

    private int JRWrapper(TestRegionBaseClass v, int in0) { return v.testFunction(in0); }

    public void runTest(TestRegionBaseClass t) {
        testHarness(t, 1);
    }
};
