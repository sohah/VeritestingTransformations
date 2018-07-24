package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import java.util.Iterator;
import java.util.Set;

public class VarTypeTable extends Table<String> {
    public VarTypeTable() {
        super("var-type table","var", "type");
    }


    public VarTypeTable clone(){
        VarTypeTable varTypeTable = new VarTypeTable();
        varTypeTable.tableName = this.tableName;
        varTypeTable.label1 = this.label1;
        varTypeTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while(iter.hasNext()){
            Integer key = iter.next();
            String value = this.lookup(key);
            varTypeTable.add(new Integer(key.intValue()), value);
        }
        return varTypeTable;
    }
}
