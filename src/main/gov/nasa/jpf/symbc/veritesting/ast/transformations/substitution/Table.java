package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

public class Table<T> {
    protected HashMap<Integer, T> table;
    protected String tableName;
    protected String label1;
    protected String label2;

    public Table(String tableName, String label1, String label2){
        this.table = new HashMap<>();
        this.tableName = tableName;
        this.label1 = label1;
        this.label2 = label2;
    }

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

    public void add(Integer v1, T v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println(v1 + " --------- " + v2));
    }
    
    public void updateKeys(Integer oldKey, Integer newKey){
        Set<Integer> keys = table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while(iter.hasNext()){
            Integer key = iter.next();
            T value = table.get(key);
            if(key == oldKey){
                table.remove(key);
                table.put(newKey, value);
            }
        }
    }
}
