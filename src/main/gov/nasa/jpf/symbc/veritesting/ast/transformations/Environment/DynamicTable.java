package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;


import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.Variable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

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

    public DynamicTable(StaticTable slotParamTable, HashMap<Integer, Variable> varToNumMap, String s, String var, String s1, int uniqueNum) {
        int paramSize = slotParamTable.table.size();

        for(int i =0; i<paramSize; i++){
            Variable uniqueVar = varToNumMap.get(i + 1);
            if(uniqueVar != null){
                this.add(uniqueVar, (V) slotParamTable.lookup(i+1));
            }
            else{
                String varId = Integer.toString(i+1);
                varId = varId.concat("$");
                varId = varId.concat(Integer.toString(uniqueNum));
                WalaVarExpr walaVar = new WalaVarExpr(i+1, varId);
                this.add(walaVar,(V) slotParamTable.lookup(i+1));
            }
        }
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
