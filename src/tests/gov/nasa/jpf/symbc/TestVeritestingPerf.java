package gov.nasa.jpf.symbc;

import com.ibm.wala.util.intset.Bits;
import org.junit.Test;

public class TestVeritestingPerf extends gov.nasa.jpf.symbc.InvokeTest {
    private static final String CLASSPATH = "+classpath=../build/tests,../lib/com.ibm.wala.util-1.4.4-SNAPSHOT.jar";
    protected static final String INSN_FACTORY = "+jvm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory";
    private static final String SYM_METHOD =
            ",gov.nasa.jpf.symbc.TestVeritestingPerf.testHarness(con#sym)";
    private static final String VM_STORAGE = "+vm.storage.class=nil";
    private static final String DEBUG = "+symbolic.debug=false";
    private static final String SOLVER = "+symbolic.dp=z3bitvector";
    private static final String LISTENER = "+listener=gov.nasa.jpf.symbc.VeritestingListener";
    private static final String VERITESTING_MODE_4 = "+veritestingMode=4";
    private static final String VERITESTING_MODE_3 = "+veritestingMode=3";
    private static final String REPORTER_CONFIG = "+test.report.console.finished=result,statistics";
    private static final String VERITESTING_DEBUG = "+veritestingDebug = 0";



    private static final String[] FULL_INT_VM4 = {INSN_FACTORY, CLASSPATH,
            SYM_METHOD, VM_STORAGE, DEBUG, SOLVER,VERITESTING_DEBUG,
            "+symbolic.min_int=-2147483648", "+symbolic.max_int=2147483647", REPORTER_CONFIG,
            LISTENER,
            VERITESTING_MODE_4};

    public static void main(String[] args) {
        hideSummary = false;
        runTestsOfThisClass(args);
        System.out.println("inside main");
    }

    @Test
    public void testSimple1() {
        hideSummary = false;
        if (verifyNoPropertyViolation(FULL_INT_VM4)) {
            TestVeritestingPerf test = new TestVeritestingPerf();
            test.testHarness(new Simple1(), 0);
        }
    }

    class VeritestingPerf {
        void BeginNoVeritest(){};
        void EndNoVeritest(){};
        int testFunction(int x){return 0;};
    }

    private void testHarness(VeritestingPerf v, int in0) {
        int outSPF = SPFWrapper(v, in0);
        int outJR = JRWrapper(v, in0);
        checkEquality(v, outSPF, outJR);
    }

    private void checkEquality(VeritestingPerf v, int outSPF, int outJR) {
        v.BeginNoVeritest();
        if (outSPF == outJR) System.out.println("Match");
        else System.out.println("Mismatch");
//        assert(outSPF == outJR);
        v.EndNoVeritest();
    }

    private int SPFWrapper(VeritestingPerf v, int in0) {
        v.BeginNoVeritest();
        int ret = v.testFunction(in0);
        v.EndNoVeritest();
        return ret;
    }

    private int JRWrapper(VeritestingPerf v, int in0) { return v.testFunction(in0); }

    class Simple1 extends VeritestingPerf {
        int testFunction(int in0) {
            return simple1(in0);
        }
        public int simple1(int x) {
            int count;
            if (x != 0) {
                count = 3;
            } else {
                count = 4;
            }
            return count;
        }
    }


}