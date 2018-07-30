package gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.Table;

import java.util.Iterator;
import java.util.Set;

public class WalaNumTypesTable extends Table<String> {
    public WalaNumTypesTable() {
        super("WalaNumTypesTable", "Wala value number", "type name");
    }

    public WalaNumTypesTable clone(){
        WalaNumTypesTable walaNumTypesTable = new WalaNumTypesTable();
        walaNumTypesTable.tableName = this.tableName;
        walaNumTypesTable.label1 = this.label1;
        walaNumTypesTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while(iter.hasNext()){
            Integer key = iter.next();
            String type = this.lookup(key);
            walaNumTypesTable.add(new Integer(key.intValue()),type);
        }
        return walaNumTypesTable;
    }
}
