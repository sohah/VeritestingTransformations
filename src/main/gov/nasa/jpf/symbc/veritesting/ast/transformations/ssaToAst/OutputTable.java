package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Table;

import java.util.*;

public class OutputTable extends Table<Integer>{
    public OutputTable(StackSlotTable stackSlotTable) {
        super("Region Output Table", "slot", "var");
        computeOutputVars(stackSlotTable);
    }

    private OutputTable(){
        super();
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

    @Override
    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println(v1 + " --------- !w" + v2));
    }

    public OutputTable clone(){
        OutputTable outputTable = new OutputTable();
        outputTable.tableName = this.tableName;
        outputTable.label1 = this.label1;
        outputTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while(iter.hasNext()){
            Integer key = iter.next();
            int value = this.lookup(key);
            outputTable.add(new Integer(key.intValue()), value);
        }
        return outputTable;
    }


    public void makeUniqueKey(int unique){
        Object[] keys = table.keySet().toArray();
        for(int i=0; i < keys.length; i++){
            String varId = Integer.toString(table.get(keys[i]));
            varId = varId.concat(Integer.toString(unique));
            table.put((Integer) keys[i], Integer.valueOf(varId));
        }
    }
}
