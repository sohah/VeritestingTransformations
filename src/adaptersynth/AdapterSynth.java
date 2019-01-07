import gov.nasa.jpf.symbc.veritesting.AdapterSynth.ArgSubAdapter;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.GetInputsFromFile;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.TestInput;

import java.io.*;
import java.util.ArrayList;

import static java.lang.System.exit;

public class AdapterSynth {
    final long const_lb = 0;
    final long const_ub = 2;
    final int n_args_target = 3;

    ArgSubAdapter argSub;
    ArrayList<TestInput> testInputs = null;
    Boolean isAdapterSearch = null;

    public AdapterSynth() {
        int[] i_val = new int[]{0,0,0,0,0,0};
        int[] b_val = new int[]{0,0,0,0,0,0};
        int[] c_val = new int[]{0,0,0,0,0,0};
        boolean[] i_is_const = new boolean[]{false,false,false,false,false,false};
        boolean[] b_is_const = new boolean[]{false,false,false,false,false,false};
        boolean[] c_is_const = new boolean[]{false,false,false,false,false,false};
        argSub = new ArgSubAdapter(i_is_const, i_val, b_is_const, b_val, c_is_const, c_val);
    }

    boolean testHarness_NoVeritest(AdapterRegionBase v, TestInput input) {
        boolean isMatch;
        Outputs targetOutput = v.testFunction1(input);
        Outputs referenceOutput = adaptedTestFunction_NoVeritest(v, input);
        if (targetOutput.equals(referenceOutput)) {
            System.out.println("Match");
            isMatch = true;
        }
        else {
            System.out.println("Mismatch");
            isMatch = false;
        }
        return isMatch;
    }

    public void runTests_NoVeritest(AdapterRegionBase t) {
        System.out.println("Number of test inputs: " + testInputs.size());
//        if (!isAdapterSearch) System.out.println("Starting new counterexample search for adapter: " + argSub);
        boolean isAllMatch = true;
        for (TestInput testInput: testInputs) {
//            if (isAdapterSearch) System.out.println("Starting new adapter search for test input: " + testInput);
            boolean isThisMatch = testHarness_NoVeritest(t, testInput);
            if (isThisMatch) {
                if (!isAdapterSearch) exit(0);
            } else {
                // if isAdapterSearch, ask SPF to abort this execution path
                // else save the model and stop executing this counterexample search step
                if (isAdapterSearch) {
                    System.out.println("exiting because of mismatch in adapter search");
//                    abortExecutionPath();
                    exit(0);
                } else {
                    concretizeCounterExample();
                    throw new IllegalArgumentException("Found a counterexample");
                }
            }
            isAllMatch = isThisMatch & isAllMatch;
        }
        if (isAdapterSearch && isAllMatch) {
            concretizeAdapter(); // SPF will concretize the adapter and write it to the "args" file
            throw new IllegalArgumentException("Found an adapter");
        } else exit(0);
        // should never be reached because
        // 1. adapter searches that ran into even a single mismatch should have aborted those execution paths
        // 2. counterexample searches that ran into even a single match should have aborted those execution paths
//        assert false;
    }

    // Methods that instruction SPF to do something in SPFAdapterSynth.java
    private void concretizeCounterExample() {}
    private void abortExecutionPath() {}
    private void concretizeAdapter() {}

    public Outputs adaptedTestFunction_NoVeritest(AdapterRegionBase v, TestInput input) {
        TestInput inputAdapted = adapt(argSub, input);
        System.out.println("original inputs: " + input + ", adapted inputs: " + inputAdapted);
        return v.testFunction2(inputAdapted);
    }

    private TestInput adapt(ArgSubAdapter argSub, TestInput input) {
        TestInput ret = new TestInput();
        int i_val1, i_val2, i_val3;
        boolean b_val1, b_val2, b_val3;
        int in0 = input.in[0];
        int in1 = input.in[1];
        int in2 = input.in[2];
        input.in = new int[]{in0, in1, in2};
        for(int i=0; i < n_args_target; i++) {
            i_val1 = argSub.i_val[i];
//            i_val2 = input.in[i_val1];
            // The commented-out version prevents summary instantiation because our simplification cannot discard the
            // possibility of a out-of-bounds access by i_val1
//            i_val3 = argSub.i_is_const[i]? i_val1 : input.in[i_val1];
            // Hence, I used a hard-coded ITE to allow veritesting to summarize without involving the array access.
            // This ITE still forces branching by SPF
            i_val3 = argSub.i_is_const[i]? i_val1 : (i_val1 == 0 ? in0 : (i_val1 == 1 ? in1 : in2));
            ret.in[i] = i_val3;
            System.out.println("after adapt branch");
        }
        /*for(int i=0; i < 6; i++) {
            b_val1 = (argSub.b_val[i] != 0);
            b_val2 = input.b[argSub.b_val[i]];
            b_val3 = argSub.b_is_const[i] ? b_val1: b_val2;
            ret.b[i] = b_val3;
            System.out.print("");
        }*/
//        for(int i=0; i < 6; i++) {
//            ret.c[i] = argSub.c_is_const[i] ? (char) argSub.c_val[i] : input.c[argSub.c_val[i]];
//        }
        return ret;
    }

    public static void main(String[] args) {
        System.out.println("System.getenv(STEP) = " + System.getenv("STEP"));
        AdapterSynth adapterSynth = new AdapterSynth();
        if (args.length == 0) {
            if (!System.getenv("STEP").equals("A")) {
                args = new String[]{"adapter"};
                adapterSynth.isAdapterSearch = false;
            } else {
                args = new String[]{"tests"};
                adapterSynth.isAdapterSearch = true;
            }
        }
        if (args[0].equals("writeRandomTest")) {
            AdapterSynthUtil.writeRandomTest(args[1]);
            exit(0);
        } else if (args[0].equals("writeIdentityAdapter")) {
            AdapterSynthUtil.writeInitialAdapter(args[1], ArgSubAdapter.identityAdapter());
            exit(0);
        } else if (args[0].equals("writeZeroAdapter")) {
            AdapterSynthUtil.writeInitialAdapter(args[1], ArgSubAdapter.zeroAdapter());
            exit(0);
        }
        runOneStep_NoVeritest(args[0], adapterSynth);
    }


    private static void runOneStep_NoVeritest(String arg, AdapterSynth adapterSynth) {
        try {
            GetInputsFromFile getInputsFromFile = new GetInputsFromFile(arg, adapterSynth.isAdapterSearch).invoke();
//            adapterSynth.isAdapterSearch = getInputsFromFile.getC().equals('A');
            adapterSynth.isAdapterSearch = System.getenv("STEP").equals("A");
            if (!adapterSynth.isAdapterSearch) {
                System.out.println("Starting new counterexample search for adapter: " + adapterSynth.argSub);
                adapterSynth.argSub = getInputsFromFile.getAdapter();
                adapterSynth.testInputs = new ArrayList<>();
                adapterSynth.testInputs.add(AdapterSynthUtil.symbolicTestInput(/*0,0,0,0,0,0,
                        false,false,false,false,false,false,
                        '0','0','0','0','0','0'*/));
            } else {
                System.out.println("Starting new adapter search for test inputs ");
                adapterSynth.argSub = AdapterSynthUtil.symbolicArgSubAdapter(adapterSynth.argSub/*,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0*/);
//                if (!isIdentityAdapter(adapterSynth.argSub)) exit(0); // hack to check if identity adapter works
                adapterSynth.testInputs = getInputsFromFile.getTestInputs();
            }
        } catch (FileNotFoundException e) {
            e.printStackTrace();
            System.exit(2);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(3);
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
            System.exit(4);
        }
        boolean feasibleAdaptation;
        feasibleAdaptation = AdapterSynthUtil.isFeasibleAdaptation(adapterSynth);
        if (feasibleAdaptation) {
            System.out.println("feasible path");
            adapterSynth.runTests_NoVeritest(new TestFunctions());
        } else {
            System.out.println("infeasible path");
//            adapterSynth.abortExecutionPath();
            exit(0);
        }
    }
}

