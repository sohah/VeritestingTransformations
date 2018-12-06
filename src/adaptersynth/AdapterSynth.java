//import gov.nasa.jpf.symbc.Debug;
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
        for (int i=0; i < 6; i++) {
//            i_is_const[i] = Debug.makeSymbolicBoolean("i_is_const" + i);
//            i_val[i] = Debug.makeSymbolicInteger("i_val" + i);
//            b_is_const[i] = Debug.makeSymbolicBoolean("b_is_const" + i);
//            b_val[i] = Debug.makeSymbolicInteger("b_val" + i);
//            c_is_const[i] = Debug.makeSymbolicBoolean("c_is_const" + i);
//            c_val[i] = Debug.makeSymbolicInteger("c_val" + i);
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
            // if isAdapterSearch, ask SPF to abort this execution path
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
            adapterSynth.tests = getInputsFromFile.getTestInputs();
            adapterSynth.isAdapterSearch = getInputsFromFile.getC().equals('A');
            adapterSynth.argSub = getInputsFromFile.getAdapter();

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
        adapterSynth.runAdapterSynth(new TestAndIte());
    }

    private static void writeRandomTest(String arg) {
        try {
            TestInput input = null;
            GetInputsFromFile getInputsFromFile = new GetInputsFromFile(arg).invoke();
            input = getInputsFromFile.getTestInputs().get(0);
            Character c = getInputsFromFile.getC();
            System.out.println("Previous test: c = " + c + ", input = " + input);
            input = new TestInput();
            FileOutputStream file = new FileOutputStream(arg);
            ObjectOutputStream out = new ObjectOutputStream(file);
            out.writeChar('A');
            out.writeObject(input);
            out.close();
            file.close();
            System.out.println("New test written: " + input);
        }
        catch (IOException ex) {
            ex.printStackTrace();
            System.out.println("failed to write random test");
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
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
                    TestInput input = (TestInput)in.readObject();
                    while (input != null) {
                        testInputs.add(input);
                        try {
                            input = (TestInput) in.readObject();
                        } catch (EOFException e) { input = null; }
                    }
                    adapter = null;
                    break;
                case 'C':
                    adapter = (ArgSubAdapter) in.readObject();
                    // Nothing should exist in the input file after the adapter
                    assert in.readObject() == null;
                    testInputs = null;
                    break;
                default: throw new IllegalArgumentException("Input file does not have the right format");
            }

            fileInputStream.close();
            return this;
        }
    }
}

