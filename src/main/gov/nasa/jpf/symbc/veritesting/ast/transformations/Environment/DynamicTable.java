package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;


import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.Variable;

import java.util.*;

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


    public DynamicTable(StaticTable staticTable, int uniqueNum) throws CloneNotSupportedException, StaticRegionException {
        super(staticTable.tableName, staticTable.label1, staticTable.label2);

        List keys = new ArrayList(staticTable.table.keySet());
        Collections.sort(keys);
        Collections.reverse(keys);
        Iterator itr = keys.iterator();
        while(itr.hasNext()){
            Integer oldWalaId = (Integer) itr.next();
            WalaVarExpr newKey = new WalaVarExpr(oldWalaId);
            newKey = newKey.makeUnique(uniqueNum);
            table.put(newKey, (V) staticTable.lookup(oldWalaId));
        }
    }

    /**
     * Returns all keys of the table.
     */

    public ArrayList<Variable> getKeys() {
        return new ArrayList<>(table.keySet());
    }


    /**
     * Appends a postfix to each key in the table.
     * @param unique A unique postfix.
     */
    public void makeClonableVarUniqueKey(int unique) throws CloneNotSupportedException, StaticRegionException {
        List keys = new ArrayList(table.keySet());
        Collections.sort(keys);
        Collections.reverse(keys);
        Iterator itr = keys.iterator();
        while(itr.hasNext()){
            Variable oldKey = (Variable) itr.next();
            assert(oldKey instanceof CloneableVariable);
            Variable newKey = ((CloneableVariable)oldKey).clone();
            assert(newKey instanceof CloneableVariable);
            newKey = ((CloneableVariable)newKey).makeUnique(unique);
            table.put(newKey, table.get(oldKey));
            table.remove(oldKey);
        }
    }
}
