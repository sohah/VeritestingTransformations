package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;

import java.util.HashMap;
import java.util.Set;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySSAVisitor.ARRAY_SUBSCRIPT_BASE;

public class GlobalArraySubscriptMap {
    public final HashMap<ArrayRef, Integer> table;
    protected final String tableName = "Global Subscript Map";
    protected final String label1 = "ArrayRef";
    protected final String label2 = "subscript";

    public GlobalArraySubscriptMap(){
        this.table = new HashMap<>();
    }

    // returns -1 if the key isn't found
    public int lookup(ArrayRef key) {
        int ret = -1;
        if (key != null) {
            for (ArrayRef array: table.keySet()) {
                if (array.ref == key.ref && array.index.equals(key.index))
                    ret = table.get(array);
            }
        }
        else {
            throw new IllegalArgumentException("Cannot lookup the value of a null " + label1 + ".");
        }
        return ret;
    }

    public void add(ArrayRef v1, Integer v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void remove(ArrayRef key) {
        if (lookup(key) != -1)
            for (ArrayRef array: table.keySet()) {
                if (array.ref == key.ref && array.index.equals(key.index))
                    table.remove(array);
            }
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }

    public Set<ArrayRef> getKeys(){
        return table.keySet();
    }

    @Override
    protected GlobalArraySubscriptMap clone() {
        GlobalArraySubscriptMap map = new GlobalArraySubscriptMap();
        this.table.forEach(map::add);
        return map;
    }

    public void updateValue(ArrayRef arrayRef, Integer p) {
        for(ArrayRef key: table.keySet()) {
            if(key.equals(arrayRef)) {
                table.put(key, p);
            }
        }
    }

    public Integer createSubscript(ArrayRef arrayRef) {
        if (lookup(arrayRef) != -1) {
            int ret = lookup(arrayRef);
            updateValue(arrayRef, ret+1);
            return ret+1;
        }
        else {
            add(arrayRef, ARRAY_SUBSCRIPT_BASE + 1);
            return ARRAY_SUBSCRIPT_BASE + 1;
        }
    }
}


