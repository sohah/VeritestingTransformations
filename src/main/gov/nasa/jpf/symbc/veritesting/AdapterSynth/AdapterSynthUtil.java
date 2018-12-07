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

public class AdapterSynthUtil {
    public static void runAdapterSynth(ThreadInfo ti, StackFrame curr) {
        Map<String, Object> map = null;
        while (!JVMDirectCallStackFrame.class.isInstance(curr)) {
            if (curr.getMethodInfo().getName().equals("concretizeAdapter")) {
                PathCondition pc;
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else return;
                map = pc.solveWithValuation();
                ArgSubAdapter argSubAdapter = new ArgSubAdapter(new boolean[6], new int[6], new boolean[6], new int[6], new boolean[6], new int[6]);
                for (int i = 0; i < 6; i++) {
                    argSubAdapter.i_is_const[i] = (((Long)map.get("i_is_const" + i)) != 0);
                    argSubAdapter.i_val[i] = Math.toIntExact((Long)map.get("i_val" + i));
                    argSubAdapter.b_is_const[i] = (((Long)map.get("b_is_const" + i)) != 0);
                    argSubAdapter.b_val[i] = Math.toIntExact((Long)map.get("b_val" + i));
                    argSubAdapter.c_is_const[i] = (((Long)map.get("c_is_const" + i)) != 0);
                    argSubAdapter.c_val[i] = Math.toIntExact((Long)map.get("c_val" + i));
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
            } else if (curr.getMethodInfo().getName().equals("abortExecutionPath")) {
                ti.getVM().getSystemState().setIgnored(true);
            }
            curr = curr.getPrevious();
        }
    }
}
