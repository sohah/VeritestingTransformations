package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Table;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

//SH: this class populates the input variables for the region. it does so by computing the first var use for slots.

public class InputTable extends Table<Integer>{
    IR ir;
    public InputTable(IR ir, StackSlotTable stackSlotTable, Stmt stmt) {
        super("Region Input Table", "var", "slot");
        this.ir = ir;
        computeInputVars(stackSlotTable);
        removeDefInputs(stmt);
    }

    private void computeInputVars(StackSlotTable stackSlotTable) {
        HashSet<Integer> allSlots = stackSlotTable.getSlots();
        Iterator<Integer> slotsIter = allSlots.iterator();
        while(slotsIter.hasNext()){
            int slot = slotsIter.next();
            Set<Integer> varsForSlot = stackSlotTable.getVarsOfSlot(slot);
            this.add(Collections.min(varsForSlot), slot);
        }
    }

    private void removeDefInputs(Stmt stmt) {
        RegionInputVisitor regionInputVisitor = new RegionInputVisitor(this);
        stmt.accept(regionInputVisitor);
    }

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }
}
