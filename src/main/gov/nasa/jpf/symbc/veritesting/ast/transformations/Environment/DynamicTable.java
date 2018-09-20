package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;


import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;

public class DynamicTable<V> extends Table<Variable, V> {

    public DynamicTable(String tableName, String label1, String label2) {
        super(tableName, label1, label2);
    }

    public DynamicTable(String tableName, String label1, String label2, ArrayList<Variable> keys, ArrayList<V> values) {
        super(tableName, label1, label2);
        for(int i= 0; i < keys.size(); i++){
            this.add(keys.get(i), values.get(i));
        }
    }


    public DynamicTable(StaticTable staticTable, HashMap<Integer, za.ac.sun.cs.green.expr.Variable> numToVarMap,
                        String tableName, String label1, String label2) {
        super(tableName, label1, label2);

        if (staticTable instanceof OutputTable)
            populateReverseDynamicTable(staticTable, numToVarMap);
        else
            populateDynamicTable(staticTable, numToVarMap);
    }

    private void populateDynamicTable(StaticTable staticTable, HashMap<Integer, Variable> numToVarMap) {
        numToVarMap.forEach((varId, varObj) -> addStaticElement(varId, varObj, staticTable));
    }


    private void populateReverseDynamicTable(StaticTable staticTable, HashMap<Integer, Variable> numToVarMap) {
        numToVarMap.forEach((varId, varObj) -> addStaticElement(varId, varObj, staticTable));
    }

    public void addStaticElement(Integer number,
                                 Variable var,
                                 StaticTable staticTable) {
        Object val = staticTable.lookup(number);
        if (val != null)
            this.add(var, (V) val);
    }

    /**
     * Returns all keys of the table.
     */

    public ArrayList<Variable> getKeys() {
        return new ArrayList<Variable>(table.keySet());
    }


    public DynamicTable<V> clone(HashMap<Variable, Variable> varToVarMap){
        DynamicTable<V> clonedTable = new DynamicTable<V>(this.tableName, this.label1, this.label2);
        varToVarMap.forEach((oldVar, newVar) -> clonedTable.add(varToVarMap.get(oldVar), this.lookup(oldVar)) );
        return clonedTable;
    }
}
