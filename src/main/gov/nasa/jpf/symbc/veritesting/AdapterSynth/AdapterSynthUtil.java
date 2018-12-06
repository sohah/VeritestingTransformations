package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import gov.nasa.jpf.jvm.JVMDirectCallStackFrame;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

public class AdapterSynthUtil {
    public static void runAdapterSynth(ThreadInfo ti, StackFrame curr) {
        while (!JVMDirectCallStackFrame.class.isInstance(curr)) {
            if (curr.getMethodInfo().getName().equals("concretizeAdapter")) {
                PathCondition pc;
                if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
                    pc = ((PCChoiceGenerator) (ti.getVM().getSystemState().getChoiceGenerator())).getCurrentPC();
                } else return;
                pc.solve();
            } else if (curr.getMethodInfo().getName().equals("abortExecutionPath")) {
                ti.getVM().getSystemState().setIgnored(true);
            }
            curr = curr.getPrevious();
        }
    }
}
