public class TestVeritesting {


    void testHarness(VeritestingPerf v, int in0) {
        int outSPF = SPFWrapper(v, in0);
        int outJR = JRWrapper(v, in0);
        checkEquality(v, outSPF, outJR);
    }

    class VeritestingPerf {
        int testFunction(int x){return 0;}
    }

    private void checkEquality(VeritestingPerf v, int outSPF, int outJR) {
        if (outSPF == outJR) System.out.println("Match");
        else System.out.println("Mismatch");
//        assert(outSPF == outJR);
    }

    private int SPFWrapper(VeritestingPerf v, int in0) {
        return NoVeritest(v, in0);
    }

    int NoVeritest(VeritestingPerf v, int in0){ return SPFWrapperInner(v, in0); }

    private int SPFWrapperInner(VeritestingPerf v, int in0) {
        int ret = v.testFunction(in0);
        return ret;
    }

    private int JRWrapper(VeritestingPerf v, int in0) { return v.testFunction(in0); }

    public int simple_region(int x) {
        int count;
        if (x != 0) {
            count = 3;
        } else {
            count = 4;
        }
        return count;
    }

    class Simple1 extends VeritestingPerf {
        int testFunction(int in0) {
            return simple_region(in0);
        }
    }

    public void runTests() {
        testHarness(new Simple1(), 1);
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        t.runTests();
    }

};
