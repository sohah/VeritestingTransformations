package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.Expression;

import java.util.*;

/**
 * An environment table that maps FieldRefVarExpr (field expressions) to types.
 */
public class FieldRefTypeTable extends StringTable<String> {

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
    public FieldRefTypeTable clone() {
        FieldRefTypeTable FieldRefTypeTable = new FieldRefTypeTable();
        FieldRefTypeTable.tableName = this.tableName;
        FieldRefTypeTable.label1 = this.label1;
        FieldRefTypeTable.label2 = this.label2;
        Set<String> keys = this.table.keySet();
        Iterator<String> iter = keys.iterator();
        while (iter.hasNext()) {
            String key = iter.next();
            String type = this.lookup(key);
            FieldRefTypeTable.add(new String(key), type);
        }
        return FieldRefTypeTable;
    }

    public String lookup(Expression expr) {
        if (WalaVarExpr.class.isInstance(expr)) return null;
        if (FieldRefVarExpr.class.isInstance(expr)) {
            return table.getOrDefault(((FieldRefVarExpr)expr).getName(), null);
        }
        return null;
    }

}

