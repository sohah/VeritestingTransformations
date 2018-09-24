package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;

import java.util.HashMap;
import java.util.Set;

public class ArraySubscriptMap {
    public final HashMap<ArrayRef, SubscriptPair> table;
    protected final String tableName = "Path Subscript Map";
    protected final String label1 = "ArrayRef";
    protected final String label2 = "subscript";

    public ArraySubscriptMap(){
        this.table = new HashMap<>();
    }

    // returns -1 if the key isn't found
    public SubscriptPair lookup(ArrayRef key) {
        SubscriptPair ret = null;
        if (key != null) {
            for (ArrayRef arrayRef: table.keySet()) {
                if (arrayRef.ref == key.ref && arrayRef.index.equals(key.index))
                    ret = table.get(arrayRef);
            }
        }
        else {
            throw new IllegalArgumentException("Cannot lookup the value of a null " + label1 + ".");
        }
        return ret;
    }

    public void add(ArrayRef v1, SubscriptPair v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void remove(ArrayRef key) {
        if (lookup(key) != null)
            for (ArrayRef field: table.keySet()) {
                if (field.ref == key.ref && field.index.equals(key.index))
                    table.remove(field);
            }
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }

    public void updateKeys(ArrayRef oldKey, ArrayRef newKey){
        for(ArrayRef key: table.keySet()) {
            SubscriptPair value = table.get(key);
            if(key.equals(oldKey)) {
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }

    public Set<ArrayRef> getKeys(){
        return table.keySet();
    }

    @Override
    protected ArraySubscriptMap clone() {
        ArraySubscriptMap map = new ArraySubscriptMap();
        this.table.forEach((key, value) -> {
            map.add(key, value);
        });
        return map;
    }

    public void updateValue(ArrayRef arrayRef, SubscriptPair p) {
        for(ArrayRef key: table.keySet()) {
            if(key.equals(arrayRef)) {
                table.put(key, p);
            }
        }
    }
}

