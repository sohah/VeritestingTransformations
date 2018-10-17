public class ReplaceEqCheck {

    Outputs testFunction(char in0, char in1, char in2, char in3, char in4, char in5,
                         char in6, char in7, char in8, char in9, char in10, char in11) {
        return runReplace(in0, in1, in2, in3, in4, in5, in6, in7, in8, in9, in10, in11);
    }

    Outputs runReplace(char in0, char in1, char in2, char in3, char in4, char in5,
                       char in6, char in7, char in8, char in9, char in10, char in11) {
        replace t = new replace();
        char[] ret = t.mainProcess(in0, in1, in2, in3, in4);
        Outputs outputs = new Outputs(ret);
        return outputs;
    }


    public static void main(String[] args) {
        TestVeritestingReplace t = new TestVeritestingReplace();
        ReplaceEqCheck s = new ReplaceEqCheck();
        t.runTest(s);
    }
}