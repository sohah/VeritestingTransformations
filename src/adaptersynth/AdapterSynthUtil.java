import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.ArgSubAdapter;
import gov.nasa.jpf.symbc.veritesting.AdapterSynth.TestInput;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;

public class AdapterSynthUtil {
    public static boolean isFeasibleAdaptation(AdapterSynth adapterSynth) {
        ArgSubAdapter argSub = adapterSynth.argSub;
        boolean feasibleAdaptation;
        for (int i = 0; i < 2; i++) {
            feasibleAdaptation = (!argSub.i_is_const[i] && (argSub.i_val[i] >= 0 && argSub.i_val[i] < 2)) ||
                    (argSub.i_is_const[i] && (argSub.i_val[i] >= adapterSynth.const_lb && argSub.i_val[i] <= adapterSynth.const_ub));
            if (!feasibleAdaptation) return false;
//            feasibleAdaptation = (!argSub.b_is_const[i] && (argSub.b_val[i] >= 0 && argSub.b_val[i] < 2)) ||
//                    (argSub.b_is_const[i] && (argSub.b_val[i] >= 0 && argSub.b_val[i] <= 1));
//            if (!feasibleAdaptation) return false;
            System.out.println("after feasibility check");
        }
//        feasibleAdaptation = feasibleAdaptation && !argSub.i_is_const[0] && (argSub.i_val[0] == 0) && argSub.i_is_const[1] && (argSub.i_val[1] == 1);
        return true;
    }

    public static boolean isIdentityAdapter(ArgSubAdapter argSub) {
        return argSub.equals(ArgSubAdapter.identityAdapter());
    }

    public static void writeRandomTest(String arg) {
        try {
            TestInput input = null;
            /*gov.nasa.jpf.symbc.veritesting.AdapterSynth.GetInputsFromFile getInputsFromFile = new gov.nasa.jpf.symbc.veritesting.AdapterSynth.GetInputsFromFile(arg).invoke();
            input = getInputsFromFile.getTestInputs().get(0);
            Character c = getInputsFromFile.getC();
            System.out.println("Previous test: c = " + c + ", input = " + input);*/
            input = new TestInput();
            FileOutputStream file = new FileOutputStream(arg);
            ObjectOutputStream out = new ObjectOutputStream(file);
//            out.writeChar('A');
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

    public static void writeInitialAdapter(String arg, ArgSubAdapter a) {
        try {
            FileOutputStream file = new FileOutputStream(arg);
            ObjectOutputStream out = new ObjectOutputStream(file);
//            out.writeChar('C');
            ArgSubAdapter.writeAdapter(out, a);
            out.close();
            file.close();
            System.out.println("New adapter written: " + a);
        }
        catch (IOException ex) {
            ex.printStackTrace();
            System.out.println("failed to write identity adapter");
        }
    }

    public static ArgSubAdapter symbolicArgSubAdapter(ArgSubAdapter argSubAdapter/*,
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
        /*ret.i_is_const[0] = i_is_const0; ret.i_val[0] = i_val0;
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
        ret.c_is_const[5] = c_is_const5; ret.c_val[5] = c_val5;*/
        return ret;
    }

    public static TestInput symbolicTestInput(/*int i0, int i1, int i2, int i3, int i4, int i5,
                                       boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5,
                                       char c0, char c1, char c2, char c3, char c4, char c5*/) {
        TestInput ret = new TestInput();
        ret.in = new int[]{getSymInt("i0"), getSymInt("i1"), getSymInt("i2"), getSymInt("i3"), getSymInt("i4"), getSymInt("i5")};
        ret.b = new boolean[]{getSymBool("b0"), getSymBool("b1"), getSymBool("b2"), getSymBool("b3"), getSymBool("b4"), getSymBool("b5")};
        ret.c = new char[]{getSymChar("c0"), getSymChar("c1"), getSymChar("c2"), getSymChar("c3"), getSymChar("c4"), getSymChar("c5")};
        /*ret.in = new int[]{i0, i1, i2, i3, i4, i5};
        ret.b = new boolean[]{b0, b1, b2, b3, b4, b5};
        ret.c = new char[]{c0, c1, c2, c3, c4, c5};*/
        return ret;
    }

    private static char getSymChar(String c0) {
        return Debug.makeSymbolicChar(c0 );
    }

    private static boolean getSymBool(String b0) {
        return Debug.makeSymbolicBoolean(b0 );
    }

    private static int getSymInt(String i0) {
        return Debug.makeSymbolicInteger(i0 );
    }
}
