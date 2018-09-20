package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import za.ac.sun.cs.green.expr.Expression;

import java.util.*;

/**
 * An environment table that maps FieldRefVarExpr (field expressions) to types.
 */
public class FieldRefTypeTable extends CloneableVarTable<String> {

    /**
     * Default constructor.
     */
    public FieldRefTypeTable() {
        super("FieldRefTypeTable", "FieldRefVarExpr", "type");
    }

    /**
     * Clones the FieldRefTypeTable to a new FieldRefTypeTable, by creating new entries for the keys.
     * @return A new FieldRefTypeTable that has a new copy for the keys.
     */
    public FieldRefTypeTable clone() throws CloneNotSupportedException {
        FieldRefTypeTable fieldRefTypeTable = new FieldRefTypeTable();
        fieldRefTypeTable.tableName = this.tableName;
        fieldRefTypeTable.label1 = this.label1;
        fieldRefTypeTable.label2 = this.label2;
        Set<CloneableVariable> keys = this.table.keySet();
        Iterator<CloneableVariable> iter = keys.iterator();
        while (iter.hasNext()) {
            CloneableVariable key = iter.next();
            String type = this.lookup((Expression)key);
            fieldRefTypeTable.add(key.clone(), type);
        }
        return fieldRefTypeTable;
    }

    // returns null if the key isn't found
    public String lookup(Expression expr) {
        if (!FieldRefVarExpr.class.isInstance(expr)) return null;
        else return table.get(expr);
    }
}

