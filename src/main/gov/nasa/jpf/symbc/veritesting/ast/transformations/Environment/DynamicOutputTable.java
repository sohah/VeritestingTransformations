package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;


import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;

//slot -> var
public class DynamicOutputTable extends Table<Integer, Variable> {

    public DynamicOutputTable(String tableName, String label1, String label2) {
        super(tableName, label1, label2);
    }

    public DynamicOutputTable(OutputTable staticTable, HashMap<Integer, Variable> numToVarMap, String tableName, String label1, String label2) {
        super(tableName, label1, label2);
        populateDynamicTable(staticTable, numToVarMap);
    }

    private void populateDynamicTable(OutputTable outputTable, HashMap<Integer, Variable> numToVarMap) {
        for (Integer varId : numToVarMap.keySet()) {
            for (Integer slotId : outputTable.getKeys()) {
                if (outputTable.lookup(slotId) == varId)
                    this.add(slotId, numToVarMap.get(varId));
            }
        }
    }


    /**
     * Returns all keys of the table.
     */

    public ArrayList<Integer> getKeys() {
        return new ArrayList<Integer>(this.table.keySet());
    }

    public DynamicOutputTable clone(HashMap<Variable, Variable> varToVarMap){
        DynamicOutputTable clonedTable = new DynamicOutputTable(this.tableName, this.label1, this.label2);

        for (Variable oldVar : varToVarMap.keySet()) {
            for (Integer slotId : this.getKeys()) {
                if (this.lookup(slotId) == oldVar)
                    clonedTable.add(slotId, varToVarMap.get(oldVar));
            }
        }
        return clonedTable;
    }

}
