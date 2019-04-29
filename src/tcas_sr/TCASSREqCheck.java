
import examples.Outputs;

public class TCASSREqCheck {

    Outputs testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                         int in6, int in7, int in8, int in9, int in10, int in11) {
        return runTCAS(in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
    }

    Outputs runTCAS(int in0, int in1, int in2, int in3, int in4, int in5,
                   int in6, int in7, int in8, int in9, int in10, int in11) {
        tcas_singlereturn t = new tcas_singlereturn();
        t.mainProcess(in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
//        tcas_singlereturn.mainProcess(in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
        return tcas_singlereturn.getOutputs();
    }


    public static void main(String[] args) {
        TestVeritestingTCASSR t = new TestVeritestingTCASSR();
        TCASSREqCheck s = new TCASSREqCheck();
        t.runTest(s);
    }
}