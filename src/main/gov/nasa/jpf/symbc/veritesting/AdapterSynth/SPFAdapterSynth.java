package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import gov.nasa.jpf.jvm.JVMDirectCallStackFrame;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.Map;

public class SPFAdapterSynth {
    public static void runAdapterSynth(ThreadInfo ti, StackFrame curr) {
        Map<String, Object> map = null;
//        while (!JVMDirectCallStackFrame.class.isInstance(curr)) {
            if (curr.getMethodInfo().getName().equals("concretizeAdapter")) {
                PathCondition pc;
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else return;
                map = pc.solveWithValuation();
                ArgSubAdapter argSubAdapter = ArgSubAdapter.randomAdapter();
                for (int i = 0; i < 6; i++) {
                    argSubAdapter.i_is_const[i] = (getVal(map, "i_is_const" + i) != 0);
                    argSubAdapter.i_val[i] = Math.toIntExact(getVal(map, "i_val" + i));
                    argSubAdapter.b_is_const[i] = ((getVal(map, "b_is_const" + i)) != 0);
                    argSubAdapter.b_val[i] = Math.toIntExact(getVal(map,"b_val" + i));
                    argSubAdapter.c_is_const[i] = ((getVal(map, "c_is_const" + i)) != 0);
                    argSubAdapter.c_val[i] = Math.toIntExact(getVal(map, "c_val" + i));
                }
                FileOutputStream file = null;
                ObjectOutputStream out = null;
                try {
                    file = new FileOutputStream("args");
                    out = new ObjectOutputStream(file);
                    out.writeChar('C');
                    ArgSubAdapter.writeAdapter(out, argSubAdapter);
                    out.close();
                    file.close();
                } catch (FileNotFoundException e) {
                    e.printStackTrace();
                } catch (IOException e) {
                    e.printStackTrace();
                }
                System.out.println("concretizeAdapter wrote adapter: " + argSubAdapter);
            } else if (curr.getMethodInfo().getName().equals("abortExecutionPath")) {
                ti.getVM().getSystemState().setIgnored(true);
            } else if (curr.getMethodInfo().getName().equals("concretizeCounterExample")) {
                PathCondition pc;
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else return;
                map = pc.solveWithValuation();
                TestInput input = new TestInput();
                for (int i = 0; i < 6; i++) {
                    if (map.containsKey("i" + i))
                        input.in[i] = Math.toIntExact(((Long) map.get("i" + i)));
                    else input.in[i] = 0;
                    if (map.containsKey("b" + i))
                        input.b[i] = (((Long) map.get("b" + i)) != 0);
                    else input.b[i] = true;
                    if (map.containsKey("c" + i))
                        input.c[i] = (char)Math.toIntExact(((Long) map.get("c" + i)));
                    else input.c[i] = 0;
                }
                FileOutputStream file;
                ObjectOutputStream out;
                try {
                    file = new FileOutputStream("args");
                    out = new ObjectOutputStream(file);
                    out.writeChar('A');
                    TestInput.writeTestInput(out, input);
                    out.close();
                    file.close();
                } catch (FileNotFoundException e) {
                    e.printStackTrace();
                } catch (IOException e) {
                    e.printStackTrace();
                }
                System.out.println("concretizeCounterExample wrote counterExample: " + input);
            }
//            curr = curr.getPrevious();
//        }
    }

    private static Long getVal(Map<String, Object> map, String s) {
        if (map.containsKey(s))
            return (Long)map.get(s);
        else return 0L;
    }
}
