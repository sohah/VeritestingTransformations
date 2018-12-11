import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.ArgSubAdapter;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.TestInput;

import java.io.*;

import static java.lang.System.exit;

public class AdapterSynth {
    ArgSubAdapter argSub;
    TestInput testInput = null;
    Boolean isAdapterSearch = null;
    private static int symIntCount = 0, symBooleanCount = 0, symCharCount = 0;

    public AdapterSynth() {
        int[] i_val = new int[]{0,0,0,0,0,0};
        int[] b_val = new int[]{0,0,0,0,0,0};
        int[] c_val = new int[]{0,0,0,0,0,0};
        boolean[] i_is_const = new boolean[]{false,false,false,false,false,false};
        boolean[] b_is_const = new boolean[]{false,false,false,false,false,false};
        boolean[] c_is_const = new boolean[]{false,false,false,false,false,false};
        argSub = new ArgSubAdapter(i_is_const, i_val, b_is_const, b_val, c_is_const, c_val);
    }

    public ArgSubAdapter symbolicArgSubAdapter(ArgSubAdapter argSubAdapter/*,
                                               boolean i_is_const0, int i_val0,
                                               boolean i_is_const1, int i_val1,
                                               boolean i_is_const2, int i_val2,
                                               boolean i_is_const3, int i_val3,
                                               boolean i_is_const4, int i_val4,
                                               boolean i_is_const5, int i_val5,
                                               boolean b_is_const0, int b_val0,
                                               boolean b_is_const1, int b_val1,
                                               boolean b_is_const2, int b_val2,
                                               boolean b_is_const3, int b_val3,
                                               boolean b_is_const4, int b_val4,
                                               boolean b_is_const5, int b_val5,
                                               boolean c_is_const0, int c_val0,
                                               boolean c_is_const1, int c_val1,
                                               boolean c_is_const2, int c_val2,
                                               boolean c_is_const3, int c_val3,
                                               boolean c_is_const4, int c_val4,
                                               boolean c_is_const5, int c_val5*/) {
        ArgSubAdapter ret = argSubAdapter;
        ret.i_is_const[0] = getSymBool("i_is_const0"); ret.i_val[0] = getSymInt("i_val0");
        ret.i_is_const[1] = getSymBool("i_is_const1"); ret.i_val[1] = getSymInt("i_val1");
        ret.i_is_const[2] = getSymBool("i_is_const2"); ret.i_val[2] = getSymInt("i_val2");
        ret.i_is_const[3] = getSymBool("i_is_const3"); ret.i_val[3] = getSymInt("i_val3");
        ret.i_is_const[4] = getSymBool("i_is_const4"); ret.i_val[4] = getSymInt("i_val4");
        ret.i_is_const[5] = getSymBool("i_is_const5"); ret.i_val[5] = getSymInt("i_val5");
        ret.b_is_const[0] = getSymBool("b_is_const0"); ret.b_val[0] = getSymInt("b_val0");
        ret.b_is_const[1] = getSymBool("b_is_const1"); ret.b_val[1] = getSymInt("b_val1");
        ret.b_is_const[2] = getSymBool("b_is_const2"); ret.b_val[2] = getSymInt("b_val2");
        ret.b_is_const[3] = getSymBool("b_is_const3"); ret.b_val[3] = getSymInt("b_val3");
        ret.b_is_const[4] = getSymBool("b_is_const4"); ret.b_val[4] = getSymInt("b_val4");
        ret.b_is_const[5] = getSymBool("b_is_const5"); ret.b_val[5] = getSymInt("b_val5");
        ret.c_is_const[0] = getSymBool("c_is_const0"); ret.c_val[0] = getSymInt("c_val0");
        ret.c_is_const[1] = getSymBool("c_is_const1"); ret.c_val[1] = getSymInt("c_val1");
        ret.c_is_const[2] = getSymBool("c_is_const2"); ret.c_val[2] = getSymInt("c_val2");
        ret.c_is_const[3] = getSymBool("c_is_const3"); ret.c_val[3] = getSymInt("c_val3");
        ret.c_is_const[4] = getSymBool("c_is_const4"); ret.c_val[4] = getSymInt("c_val4");
        ret.c_is_const[5] = getSymBool("c_is_const5"); ret.c_val[5] = getSymInt("c_val5");
        return ret;
    }

    public TestInput symbolicTestInput(/*int i0, int i1, int i2, int i3, int i4, int i5,
                                       boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                                       char c0, char c1, char c2, char c3, char c4, char c5*/) {
        TestInput ret = new TestInput();
        ret.in = new int[]{getSymInt("i0"), getSymInt("i1"), getSymInt("i2"), getSymInt("i3"), getSymInt("i4"), getSymInt("i5")};
        ret.b = new boolean[]{getSymBool("b0"), getSymBool("b1"), getSymBool("b2"), getSymBool("b3"), getSymBool("b4"), getSymBool("b5")};
        ret.c = new char[]{getSymChar("c0"), getSymChar("c1"), getSymChar("c2"), getSymChar("c3"), getSymChar("c4"), getSymChar("c5")};
        return ret;
    }

    private char getSymChar(String c0) {
        symCharCount++;
        return Debug.makeSymbolicChar(c0 );//+ symCharCount);
    }

    private boolean getSymBool(String b0) {
        symBooleanCount++;
        return Debug.makeSymbolicBoolean(b0 );//+ symBooleanCount);
    }

    private int getSymInt(String i0) {
        symIntCount++;
        return Debug.makeSymbolicInteger(i0 );//+ symIntCount);
    }

    boolean testHarness(AdapterRegionBase v, TestInput input) {
        boolean isMatch;
        Outputs targetOutput = v.testFunction1(input);
        Outputs referenceOutput = adaptedTestFunction(v, input);
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

    public void runTests(AdapterRegionBase t) {
        boolean isMatch;
        while (testInput != null) {
            System.out.println("running tests on argSub: " + argSub);
            isMatch = testHarness(t, testInput);
            if (isMatch) {
                if (isAdapterSearch) {
                    concretizeAdapter(); // SPF will concretize the adapter and write it to the "args" file
                    testInput = runNextCE(); //run the next counterexample search step, get the test from it and use it as "testInput"
                } else break;
            } else {
                // save the model if !isAdapterSearch and stop executing this counterexample search step
                // if isAdapterSearch, ask SPF to abort this execution path
                if (isAdapterSearch) abortExecutionPath();
                else {
                    concretizeCounterExample();
                    exit(0);
                }
            }
            System.out.println("Starting new adapter search for test inputs: " + testInput);
        }

        // Finished counter-example run, failed to find a single counterexample
        if (!isAdapterSearch) {
            FileOutputStream file;
            try {
                file = new FileOutputStream("args");
                ObjectOutputStream out = new ObjectOutputStream(file);
                out.writeChar('F');
                ArgSubAdapter.writeAdapter(out, argSub);
                System.out.println("failed to find counter-example, wrote adapter: " + argSub);
                out.close();
//                file.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else {
            // this code should never be reached because, in adapter search, we abort any execution path that runs
            // into a "Mismatch"
            assert false;
        }
    }

    // Runs next counter-example search step, sets the new counter-example as the test we want to adapt on
    private TestInput runNextCE() {
        TestInput ret = null;
        AdapterSynth nextAS = new AdapterSynth();
        runOneStep("args", nextAS);
        try {
            GetInputsFromFile getInputsFromFile = new GetInputsFromFile("args").invoke();
            if (getInputsFromFile.isFinalAdapter()) {
                System.out.println("No counter-example found during this step");
                assert argSub.equals(getInputsFromFile.adapter); // this assertion fails because the query for this does not have the previous PC included in for some weird reason
                printFinalAdapter();
                throw new IllegalArgumentException("Found an adapter");
            } else if (getInputsFromFile.testInput == null) {
                System.out.println("Expected a single test input from next counter-example search");
                throw new IOException();
            }
            ret = getInputsFromFile.testInput;
        } catch (IOException|ClassNotFoundException e) {
            System.out.println("Failed to load next counterexample");
            exit(-1);
        }
        return ret;
    }

    // Methods that instruction SPF to do something in AdapterSynthUtil.java
    private void concretizeCounterExample() {}
    private void abortExecutionPath() {}
    private void concretizeAdapter() {}
    private void printFinalAdapter() {  }

    public Outputs adaptedTestFunction(AdapterRegionBase v, TestInput input) {
        TestInput inputAdapted = adapt(argSub, input);
        return v.testFunction2(inputAdapted);
    }

    private TestInput adapt(ArgSubAdapter argSub, TestInput input) {
        TestInput ret = new TestInput();
        for(int i=0; i < 6; i++) {
            if (argSub.i_is_const[i]) ret.in[i] = argSub.i_val[i];
            else ret.in[i] = input.in[argSub.i_val[i]];
        }
        for(int i=0; i < 6; i++) {
            if (argSub.b_is_const[i]) ret.b[i] = (argSub.b_val[i] == 1);
            else ret.b[i] = input.b[argSub.b_val[i]];
        }
        for(int i=0; i < 6; i++) {
            if (argSub.c_is_const[i]) ret.c[i] = (char) argSub.c_val[i];
            else ret.c[i] = input.c[argSub.c_val[i]];
        }
        return ret;
    }

    public static void main(String[] args) {
        AdapterSynth adapterSynth = new AdapterSynth();
        if (args.length == 0) {
            args = new String[]{"args"};
        }
        if (args[0].equals("writeRandomTest")) {
            writeRandomTest(args[1]);
            exit(0);
        } else if (args[0].equals("writeIdentityAdapter")) {
            writeIdentityAdapter(args[1]);
            exit(0);
        }
        runOneStep(args[0], adapterSynth);
    }


    private static void runOneStep(String arg, AdapterSynth adapterSynth) {
        try {
            GetInputsFromFile getInputsFromFile = new GetInputsFromFile(arg).invoke();
            adapterSynth.isAdapterSearch = getInputsFromFile.getC().equals('A');
            if (!adapterSynth.isAdapterSearch) {
                adapterSynth.argSub = getInputsFromFile.getAdapter();
                System.out.println("Starting new counterexample search for adapter: " + adapterSynth.argSub);
                adapterSynth.testInput = adapterSynth.symbolicTestInput(/*0,0,0,0,0,0,
                        false,false,false,false,false,false,
                        '0','0','0','0','0','0'*/);
            } else {
                adapterSynth.argSub = adapterSynth.symbolicArgSubAdapter(adapterSynth.argSub/*,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0*/);
//                if (!isIdentityAdapter(adapterSynth.argSub)) exit(0); // hack to check if identity adapter works
                adapterSynth.testInput = getInputsFromFile.getTestInput();
                System.out.println("Starting new adapter search for test inputs: " + adapterSynth.testInput);
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
        boolean feasibleAdaptation = true;
        ArgSubAdapter argSub = adapterSynth.argSub;
        for (int i = 0; i < 6; i++) {
            if (!argSub.i_is_const[i]) feasibleAdaptation = feasibleAdaptation &&
                    (argSub.i_val[i] >= 0 && argSub.i_val[i] <= 5);
            if (!argSub.b_is_const[i]) feasibleAdaptation = feasibleAdaptation &&
                    (argSub.b_val[i] >= 0 && argSub.b_val[i] <= 5);
            if (!argSub.c_is_const[i]) feasibleAdaptation = feasibleAdaptation &&
                    (argSub.c_val[i] >= 0 && argSub.c_val[i] <= 5);
        }
        if (feasibleAdaptation) adapterSynth.runTests(new TestFunctions());
    }

    private static boolean isIdentityAdapter(ArgSubAdapter argSub) {
        return argSub.equals(ArgSubAdapter.identityAdapter());
    }

    private static void writeRandomTest(String arg) {
        try {
            TestInput input = null;
            /*GetInputsFromFile getInputsFromFile = new GetInputsFromFile(arg).invoke();
            input = getInputsFromFile.getTestInputs().get(0);
            Character c = getInputsFromFile.getC();
            System.out.println("Previous test: c = " + c + ", input = " + input);*/
            input = new TestInput();
            FileOutputStream file = new FileOutputStream(arg);
            ObjectOutputStream out = new ObjectOutputStream(file);
            out.writeChar('A');
            TestInput.writeTestInput(out, input);
            out.close();
            file.close();
            System.out.println("New test written: " + input);
        }
        catch (IOException ex) {
            ex.printStackTrace();
            System.out.println("failed to write random test");
        }
    }

    private static void writeIdentityAdapter(String arg) {
        try {
            ArgSubAdapter a = ArgSubAdapter.identityAdapter();
            FileOutputStream file = new FileOutputStream(arg);
            ObjectOutputStream out = new ObjectOutputStream(file);
            out.writeChar('C');
            ArgSubAdapter.writeAdapter(out, a);
            out.close();
            file.close();
            System.out.println("New adapter written: " + a);
        }
        catch (IOException ex) {
            ex.printStackTrace();
            System.out.println("failed to write random test");
        }
    }

    private static class GetInputsFromFile {
        private String arg;
        private TestInput testInput = null;
        private ArgSubAdapter adapter = null;
        private FileInputStream fileInputStream;
        private Character c;
        private boolean isFinalAdapter = false;

        public GetInputsFromFile(String arg) {
            this.arg = arg;
        }

        private boolean isFinalAdapter() { return isFinalAdapter; }

        public TestInput getTestInput() {
            return testInput;
        }

        public Character getC() {
            return c;
        }

        public ArgSubAdapter getAdapter() { return adapter; }

        public GetInputsFromFile invoke() throws IOException, ClassNotFoundException {
            /*
            Assume that the file has the format
            A
            Serialized ArgSubAdapter object
            OR
            C
            Serialized TestInput object 1
            Serialized TestInput object 2
            ...
             */
            fileInputStream = new FileInputStream(arg);
            ObjectInputStream in = new ObjectInputStream(fileInputStream);
            c = in.readChar();
            switch(c) {
                case 'A':
                    testInput = TestInput.readTestInput(in);
                    try {
                        in.readObject();
                        assert false; // there should only ever be a single test input that we want to adapt for
                    } catch (EOFException e) { }
                    adapter = null;
                    break;
                case 'C':
                    adapter = ArgSubAdapter.readAdapter(in);
                    // Nothing should exist in the input file after the adapter
                    try {
                        in.readObject();
                        assert false;
                    } catch(EOFException e) { }
                    testInput = null;
                    break;
                case 'F': //written by runTests to indicate no counterexample was found for a given adapter
                    testInput = null;
                    adapter = ArgSubAdapter.readAdapter(in);
                    isFinalAdapter = true;
                    System.out.println("read final adapter");
                    break;
                default: throw new IllegalArgumentException("Input file does not have the right format");
            }

            in.close();
//            fileInputStream.close();
            return this;
        }
    }
}

