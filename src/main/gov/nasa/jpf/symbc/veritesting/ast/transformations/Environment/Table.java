package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;

import java.util.*;

import static com.ibm.wala.shrike.bench.Slots.i;

/**
 * Base class for all environment tables.
  */


public class Table<T> {
    public final HashMap<Integer, T> table;
    protected String tableName;
    protected String label1;
    protected String label2;

    protected Table(){
        this.table = new HashMap<>();
    }

    public Table(String tableName, String label1, String label2){
        this.table = new HashMap<>();
        this.tableName = tableName;
        this.label1 = label1;
        this.label2 = label2;
    }

    /**
     * Basic lookup inside the table.
     * */
    public T lookup(Integer v) {
        if (v != null)
            return table.get(v);
        else
            try {
                throw new StaticRegionException("Cannot lookup the value of a null " + label1 + ".");
            } catch (StaticRegionException e) {
                System.out.println(e.getMessage());
            }
        return null;
    }

    /**
     * Basic add row inside the table.
     * */

    public void add(Integer v1, T v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    /**
     * Basic remove element/row inside the table.
     * */

    public void remove(Integer v1) {
         table.remove(v1);
    }

    /**
     * Basic print of the table. inside the table.
     * */

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("@w"+v1 + " --------- " + v2));
    }

    /**
     * Updates a key of the table for a specific entry.
     * */

    public void updateKeys(Integer oldKey, Integer newKey){
        Object[] keys = table.keySet().toArray();
        for(int i=0; i < keys.length; i++){
            T value = table.get(keys[i]);
            if(keys[i] == oldKey){
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }

    /**
     * Returns all keys of the table.
     * */

    public Set<Integer> getKeys(){
        return  table.keySet();
    }

    /**
     * Appends a postfix to each key in the table.
     * @param unique A unquie postfix.
     */

    public void makeUniqueKey(int unique){
        List keys = new ArrayList(table.keySet());
        Collections.sort(keys);
        Collections.reverse(keys);
        Iterator itr = keys.iterator();
        while(itr.hasNext()){
            Integer key = (Integer) itr.next();
            String varId = Integer.toString(key);
            varId = varId.concat(Integer.toString(unique));
            table.put(Integer.valueOf(varId), table.get(key));
            table.remove(key);
        }
    }

    /**
     * Merge the table with the eateries of another table.
     * */

    public void mergeTable(Table<T> t){
        this.table.putAll(t.table);
    }


}
