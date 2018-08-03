package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

//SH: this class populates the input variables for the region. it does so by computing the first var use for slots.

public class InputTable extends Table<Integer> {
    public final IR ir;

    public InputTable(IR ir, boolean isMethodRegion, SlotParamTable slotParamTable, Stmt stmt) {
        super("Region Input Table", "var", isMethodRegion ? "param" : "slot");
        this.ir = ir;
        if (isMethodRegion) // all parameters are input
            computeMethodInputVars(slotParamTable);
        else {//only first instances of vars to slots execluding defs.
            computeRegionInputVars(slotParamTable);
            removeDefInputs(stmt);
        }
    }

    private void computeMethodInputVars(SlotParamTable slotParamTable) {
        for (Integer var : slotParamTable.getKeys()) {
            this.add(var, slotParamTable.lookup(var)[0]);
        }
    }

    private void computeRegionInputVars(SlotParamTable slotParamTable) {
        HashSet<Integer> allSlots = slotParamTable.getSlots();
        Iterator<Integer> slotsIter = allSlots.iterator();
        while (slotsIter.hasNext()) {
            int slot = slotsIter.next();
            Set<Integer> varsForSlot = slotParamTable.getVarsOfSlot(slot, null, null);
            this.add(Collections.min(varsForSlot), slot);
        }
    }

    private void removeDefInputs(Stmt stmt) {
        RegionInputVisitor regionInputVisitor = new RegionInputVisitor(this);
        stmt.accept(regionInputVisitor);
    }

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        table.forEach((v1, v2) -> System.out.println("!w" + v1 + " --------- " + v2));
    }
}
