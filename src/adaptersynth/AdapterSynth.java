import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.ArgSubAdapter;

import java.util.ArrayList;

public class AdapterSynth {
    ArgSubAdapter argSub;
    ArrayList<TestInput> tests;
    boolean isAdapterSearch;

    public AdapterSynth() {
        int[] i_val = new int[6];
        int[] b_val = new int[6];
        int[] c_val = new int[6];
        boolean[] i_is_const = new boolean[6];
        boolean[] b_is_const = new boolean[6];
        boolean[] c_is_const = new boolean[6];
        for (int i=0; i < 6; i++) {
            i_is_const[i] = Debug.makeSymbolicBoolean("i_is_const" + i);
            i_val[i] = Debug.makeSymbolicInteger("i_val" + i);
            b_is_const[i] = Debug.makeSymbolicBoolean("b_is_const" + i);
            b_val[i] = Debug.makeSymbolicInteger("b_val" + i);
            c_is_const[i] = Debug.makeSymbolicBoolean("c_is_const" + i);
            c_val[i] = Debug.makeSymbolicInteger("c_val" + i);
        }
        argSub = new ArgSubAdapter(i_is_const, i_val, b_is_const, b_val, c_is_const, c_val);
    }

    void testHarness(TestRegionBaseClass v, TestInput input, boolean isLastTest) {
        Outputs targetOutput = v.testFunction(input);
        Outputs referenceOutput = adaptedTestFunction(v, input);
        if (targetOutput.equals(referenceOutput)) {
            System.out.println("Match");
            // concretize the adapter to give to the next CE search and stop executing this adapter search step
            if (isAdapterSearch && isLastTest) {
                //TODO: 1. concretize the adapter, 2. run the next counterexample search step, 3. get the test from it and add it as a new test case
                concretizeAdapter();
            }
        }
        else {
            System.out.println("Mismatch");
            // TODO: save the model if !isAdapterSearch and stop executing this counterexample search step
            // TODO: if isAdapterSearch, ask SPF to abort this execution path
            if (isAdapterSearch) abortExecutionPath();
            else saveModelAndStopSearch();
        }
    }

    private void abortExecutionPath() {
    }

    private void concretizeAdapter() {
    }

    private void saveModelAndStopSearch() {
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
        for(int i = 0; i < tests.size(); i++) {
            testHarness(t, tests.get(i), i == tests.size()-1);
        }
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

