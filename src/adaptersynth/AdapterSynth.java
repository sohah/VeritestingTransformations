import gov.nasa.jpf.symbc.veritesting.AdapterSynth.ArgSubAdapter;

import java.io.*;
import java.util.ArrayList;

import static java.lang.System.exit;

public class AdapterSynth {
    ArgSubAdapter argSub;
    ArrayList<TestInput> tests;
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

    public ArgSubAdapter symbolicArgSubAdapter(ArgSubAdapter argSubAdapter,
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
                                               boolean c_is_const5, int c_val5) {
        ArgSubAdapter ret = argSubAdapter;
        ret.i_is_const[0] = i_is_const0; ret.i_val[0] = i_val0;
        ret.i_is_const[1] = i_is_const1; ret.i_val[1] = i_val1;
        ret.i_is_const[2] = i_is_const2; ret.i_val[2] = i_val2;
        ret.i_is_const[3] = i_is_const3; ret.i_val[3] = i_val3;
        ret.i_is_const[4] = i_is_const4; ret.i_val[4] = i_val4;
        ret.i_is_const[5] = i_is_const5; ret.i_val[5] = i_val5;
        ret.b_is_const[0] = b_is_const0; ret.b_val[0] = b_val0;
        ret.b_is_const[1] = b_is_const1; ret.b_val[1] = b_val1;
        ret.b_is_const[2] = b_is_const2; ret.b_val[2] = b_val2;
        ret.b_is_const[3] = b_is_const3; ret.b_val[3] = b_val3;
        ret.b_is_const[4] = b_is_const4; ret.b_val[4] = b_val4;
        ret.b_is_const[5] = b_is_const5; ret.b_val[5] = b_val5;
        ret.c_is_const[0] = c_is_const0; ret.c_val[0] = c_val0;
        ret.c_is_const[1] = c_is_const1; ret.c_val[1] = c_val1;
        ret.c_is_const[2] = c_is_const2; ret.c_val[2] = c_val2;
        ret.c_is_const[3] = c_is_const3; ret.c_val[3] = c_val3;
        ret.c_is_const[4] = c_is_const4; ret.c_val[4] = c_val4;
        ret.c_is_const[5] = c_is_const5; ret.c_val[5] = c_val5;
        return ret;
    }

    public TestInput symbolicTestInput(int i0, int i1, int i2, int i3, int i4, int i5,
                                       boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                                       char c0, char c1, char c2, char c3, char c4, char c5) {
        TestInput ret = new TestInput();
        ret.in = new int[]{i0, i1, i2, i3, i4, i5};
        ret.b = new boolean[]{b0, b1, b2, b3, b4, b5};
        ret.c = new char[]{c0, c1, c2, c3, c4, c5};
        return ret;
    }

    void testHarness(TestRegionBaseClass v, TestInput input, boolean isLastTest) {
        Outputs targetOutput = v.testFunction(input);
        Outputs referenceOutput = adaptedTestFunction(v, input);
        if (targetOutput.equals(referenceOutput)) {
            System.out.println("Match");
            // concretize the adapter to give to the next CE search and stop executing this adapter search step
            if (isAdapterSearch && isLastTest) {
                //TODO: 1. concretize the adapter, 2. run the next counterexample search step, 3. get the test from it and add it as a new test case
                concretizeAdapter(); // SPF will concretize the adapter and write it to the "args" file
            }
        }
        else {
            System.out.println("Mismatch");
            // TODO: save the model if !isAdapterSearch and stop executing this counterexample search step
            // if isAdapterSearch, ask SPF to abort this execution path
            if (isAdapterSearch) abortExecutionPath();
            else concretizeCounterExample();
        }
    }

    private void concretizeCounterExample() {
    }

    private void abortExecutionPath() {
    }

    private void concretizeAdapter() {
    }

    public Outputs adaptedTestFunction(TestRegionBaseClass v, TestInput input) {
        TestInput inputAdapted = adapt(argSub, input);
        return v.testFunction(inputAdapted);
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

    public void runAdapterSynth(TestRegionBaseClass t) {
        for(int i = 0; i < tests.size(); i++) {
            testHarness(t, tests.get(i), i == tests.size()-1);
        }
    }

    public static void main(String[] args) {
        AdapterSynth adapterSynth = new AdapterSynth();
        if (args.length == 0) {
            args = new String[]{"args"};
        }
        if (args[0].equals("writeRandomTest")) {
            writeRandomTest(args[1]);
            exit(0);
        }
        try {
            GetInputsFromFile getInputsFromFile = new GetInputsFromFile(args[0]).invoke();
            adapterSynth.isAdapterSearch = getInputsFromFile.getC().equals('A');
            if (!adapterSynth.isAdapterSearch) {
                adapterSynth.argSub = getInputsFromFile.getAdapter();
                adapterSynth.tests = new ArrayList<>();
                adapterSynth.tests.add(adapterSynth.symbolicTestInput(0,0,0,0,0,0,
                        false,false,false,false,false,false,
                        '0','0','0','0','0','0'));
            } else {
                adapterSynth.argSub = adapterSynth.symbolicArgSubAdapter(adapterSynth.argSub,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0,
                        false, 0, false, 0,false, 0,false, 0,false, 0,false, 0);
                adapterSynth.tests = getInputsFromFile.getTestInputs();
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
        if (feasibleAdaptation) adapterSynth.runAdapterSynth(new TestAndIte());
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
//            out.writeObject(input);
            out.close();
            file.close();
            System.out.println("New test written: " + input);
        }
        catch (IOException ex) {
            ex.printStackTrace();
            System.out.println("failed to write random test");
        }
    }

    private static class GetInputsFromFile {
        private String arg;
        private ArrayList<TestInput> testInputs = null;
        private ArgSubAdapter adapter = null;
        private FileInputStream fileInputStream;
        private Character c;

        public GetInputsFromFile(String arg) {
            this.arg = arg;
        }

        public ArrayList<TestInput> getTestInputs() {
            return testInputs;
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
                    testInputs = new ArrayList<>();
                    TestInput input = TestInput.readTestInput(in);
                    while (input != null) {
                        testInputs.add(input);
                        try {
                            input = (TestInput) in.readObject();
                        } catch (EOFException e) { input = null; }
                    }
                    adapter = null;
                    break;
                case 'C':
                    adapter = ArgSubAdapter.readAdapter(in);
                    // Nothing should exist in the input file after the adapter
                    assert in.readObject() == null;
                    testInputs = null;
                    break;
                default: throw new IllegalArgumentException("Input file does not have the right format");
            }

            in.close();
            fileInputStream.close();
            return this;
        }
    }
}

