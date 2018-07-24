package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.IR;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import za.ac.sun.cs.green.expr.Expression;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

//SH: all values stored here should be in the form of a green expression

public class ValueSymbolTable extends Table<Expression> {


    public ValueSymbolTable() {
        super("var-value table", "var", "value");
    }

    public ValueSymbolTable clone(){
        ValueSymbolTable valueSymbolTable = new ValueSymbolTable();
        valueSymbolTable.tableName = this.tableName;
        valueSymbolTable.label1 = this.label1;
        valueSymbolTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while(iter.hasNext()){
            Integer key = iter.next();
            Expression value = this.lookup(key);
            valueSymbolTable.add(new Integer(key.intValue()), value);
        }
        return valueSymbolTable;
    }
}
