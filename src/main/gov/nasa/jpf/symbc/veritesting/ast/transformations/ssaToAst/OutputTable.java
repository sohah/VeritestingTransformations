package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Table;

import java.util.*;

public class OutputTable extends Table<Integer>{
    public OutputTable(StackSlotTable stackSlotTable) {
        super("Region Output Table", "slot", "var");
        computeOutputVars(stackSlotTable);
    }

    //SH: outputVars are computed by finding the maximum wala var for each
    //stackSlot.
    private void computeOutputVars(StackSlotTable stackSlotTable) {
        HashSet<Integer> allSlots = stackSlotTable.getSlots();
        Iterator<Integer> slotsIter = allSlots.iterator();
        while(slotsIter.hasNext()){
            int slot = slotsIter.next();
            Set<Integer> varsForSlot = stackSlotTable.getVarsOfSlot(slot);
            this.add(slot, Collections.max(varsForSlot));
        }
    }
}
