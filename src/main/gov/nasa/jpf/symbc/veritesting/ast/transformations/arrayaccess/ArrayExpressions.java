package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getArrayLength;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getExpression;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.getInitialArrayValues;
import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class ArrayExpressions {
    public final HashMap<Integer, Expression[]> table;
    public final HashMap<Integer, String> arrayTypesTable;
    private ThreadInfo ti;
    public int uniqueNum = -1;

    public ArrayExpressions(ThreadInfo ti) {
        table = new HashMap();
        this.ti = ti;
        arrayTypesTable = new HashMap<>();
    }

    @Override
    protected ArrayExpressions clone() {
        ArrayExpressions map = new ArrayExpressions(this.ti);
        this.table.forEach((key, value) -> {
            Expression[] newValue = new Expression[value.length];
            for (int i=0; i < value.length; i++)
                newValue[i] = value[i];
            map.add(key, new Pair<>(newValue, arrayTypesTable.get(key)));
        });
        return map;
    }

    public void add(Integer v1, Pair<Expression[], String> v2) {
        if ((v1 != null) && (v2 != null)) {
            table.put(v1, v2.getFirst());
            arrayTypesTable.put(v1, v2.getSecond());
        }
    }

    public void update(ArrayRef arrayRef, Expression value) {
        if (!table.containsKey(arrayRef.ref)) {
            Pair<Expression[], String> p = getInitialArrayValues(ti, arrayRef.ref);
            table.put(arrayRef.ref, p.getFirst());
            arrayTypesTable.put(arrayRef.ref, p.getSecond());
        }
        if (arrayRef.index instanceof IntConstant) {
            table.get(arrayRef.ref)[((IntConstant) arrayRef.index).getValue()] = value;
        } else {
            int len = getArrayLength(ti, arrayRef.ref);
            Expression oldValues[] = table.get(arrayRef.ref);
            Expression newValues[] = new Expression[len];
            for (int i=0; i<len; i++)
                newValues[i] = new GammaVarExpr(new Operation(EQ, arrayRef.index, new IntConstant(i)), value, oldValues[i]);
            table.put(arrayRef.ref, newValues);
        }
    }

    public Expression[] lookup(Integer ref) {
        return table.get(ref);
    }

    public void remove(Integer ref) {
        table.remove(ref);
    }


    public String getType(int ref) {
        if (arrayTypesTable.containsKey(ref)) return arrayTypesTable.get(ref);
        return null;
    }

    public Expression get(ArrayRef arrayRef) {
        int ref = arrayRef.ref;
        if (!table.containsKey(ref)) {
            Pair<Expression[], String> p = getInitialArrayValues(ti, ref);
            table.put(ref, p.getFirst());
            arrayTypesTable.put(ref, p.getSecond());
        }
        if (arrayRef.index instanceof IntConstant) {
            return table.get(ref)[((IntConstant) arrayRef.index).getValue()];
        } else {
            Pair<Expression, String> p = getExpression(ti, arrayRef, new Pair(table.get(ref), arrayTypesTable.get(ref)));
            return p.getFirst();
        }
    }

    public void setUniqueNum(int uniqueNum) {
        this.uniqueNum = uniqueNum;
    }

    public String toString() {
        String ret = new String();
        ret += "Array Outputs Table\n";
        Iterator itr = table.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<Integer, Expression[]> entry = (Map.Entry) itr.next();
            int ref = entry.getKey();
            Expression[] exps = entry.getValue();
            ret += "for array reference: " + ref +", expressions = \n";
            for (int i=0; i<exps.length; i++)
                ret += "" + i + ": " + exps[i].toString() + "\n";
        }
        return ret;
    }
}
