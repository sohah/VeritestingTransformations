public class TestVeritestingReplace {


    void testHarness(ReplaceEqCheck v,
                     char in0, char in1, char in2, char in3, char in4, char in5,
                     char in6, char in7, char in8, char in9, char in10, char in11) {
        Outputs outSPF = SPFWrapper(new ReplaceEqCheck(), in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
        replace.reset();
        Outputs outJR = JRWrapper(new ReplaceEqCheck(), in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
        checkEquality(v, outSPF, outJR);
    }

    private void checkEquality(ReplaceEqCheck v, Outputs outSPF, Outputs outJR) {
        if (outSPF.equals(outJR)) System.out.println("Match");
        else {
            System.out.println("Mismatch");
            assert(false);
        }
//        assert(outSPF == outJR);
    }

    private Outputs SPFWrapper(ReplaceEqCheck v, char in0, char in1, char in2, char in3, char in4, char in5,
                               char in6, char in7, char in8, char in9, char in10, char in11) {
        return NoVeritest(v, in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
    }

    // This is a special method. Call this method to prevent SPF from veritesting any regions that appear in any
    // function or method call higher up in the stack. In the future, this call to SPFWrapperInner can be changed to
    // be a generic method call if other no-veritesting methods need to be invoked.
    private Outputs NoVeritest(ReplaceEqCheck v, char in0, char in1, char in2, char in3, char in4, char in5,
                               char in6, char in7, char in8, char in9, char in10, char in11) {
        return SPFWrapperInner(v, in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
    }

    private Outputs SPFWrapperInner(ReplaceEqCheck v, char in0, char in1, char in2, char in3, char in4, char in5,
                                    char in6, char in7, char in8, char in9, char in10, char in11) {
        Outputs ret = v.testFunction(in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
        return ret;
    }

    private Outputs JRWrapper(ReplaceEqCheck v, char in0, char in1, char in2, char in3, char in4, char in5,
                              char in6, char in7, char in8, char in9, char in10, char in11) {
        return v.testFunction(in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
    }

    public void runTest(ReplaceEqCheck t) {
        testHarness(t, '1', '2', '3', '4', '5', '6',
                '6', '7', '8', '9', '0', '1');
    }
};
