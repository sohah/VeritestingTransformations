import java.util.ArrayList;

public class AdapterSynth {
    ArgSubAdapter argSub;
    ArrayList<TestInput> tests;
    boolean isAdapterSearch;

    public AdapterSynth() {
        argSub = new ArgSubAdapter();
    }

    void testHarness(TestRegionBaseClass v, TestInput input) {
        Outputs targetOutput = v.testFunction(input);
        Outputs referenceOutput = adaptedTestFunction(v, input);
        if (targetOutput.equals(referenceOutput)) {
            System.out.println("Match");
            // TODO: If this is the last test, then concretize the adapter to give to the next CE search
        }
        else {
            System.out.println("Mismatch");
            // TODO: print model if !isAdapterSearch and exit
            // TODO: if isAdapterSearch, ask SPF to abort this execution path
        }
    }

    public Outputs adaptedTestFunction(TestRegionBaseClass v, TestInput input) {
        TestInput inputAdapted = adapt(argSub, input);
        return v.testFunction(inputAdapted);
    }

    private TestInput adapt(ArgSubAdapter argSub, TestInput input) {
        for(int i=0; i < 6; i++) {
            if (argSub.i_is_const[i]) input.in[i] = argSub.i_val[i];
            else input.in[i] = input.in[argSub.i_val[i]];
        }
        for(int i=0; i < 6; i++) {
            if (argSub.b_is_const[i]) input.b[i] = (argSub.b_val[i] == 1);
            else input.b[i] = input.b[argSub.b_val[i]];
        }
        for(int i=0; i < 6; i++) {
            if (argSub.c_is_const[i]) input.c[i] = (char) argSub.c_val[i];
            else input.c[i] = input.c[argSub.c_val[i]];
        }
        return input;
    }

    public void runAdapterSynth(TestRegionBaseClass t) {
        for(TestInput input: tests)
            testHarness(t, input);
    }

    public static void main(String[] args) {
        TestRegionBaseClass testClass = new TestAndIte();
        if(args[0].equals("AdapterSearch")) {
            AdapterSynth adapterSynth = new AdapterSynth();
            adapterSynth.isAdapterSearch = true;
            adapterSynth.runAdapterSynth(testClass);
        } else if (args[0].equals("CounterexampleSearch")) {
            AdapterSynth adapterSynth = new AdapterSynth();
            adapterSynth.isAdapterSearch = false;
            int argsIndex = 1;
            for (int i=0; i<6; i++) {
                adapterSynth.argSub.i_is_const[i] = Boolean.parseBoolean(args[argsIndex++]);
                adapterSynth.argSub.i_val[i] = Integer.parseInt(args[argsIndex++]);
            }
            for (int i=0; i<6; i++) {
                adapterSynth.argSub.b_is_const[i] = Boolean.parseBoolean(args[argsIndex++]);
                adapterSynth.argSub.b_val[i] = Integer.parseInt(args[argsIndex++]);
            }
            for (int i=0; i<6; i++) {
                adapterSynth.argSub.c_is_const[i] = Boolean.parseBoolean(args[argsIndex++]);
                adapterSynth.argSub.c_val[i] = Integer.parseInt(args[argsIndex++]);
            }
            adapterSynth.runAdapterSynth(testClass);
        }
    }
}

