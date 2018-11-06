package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Operation;

import java.util.HashMap;

import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySSAVisitor.getExpression;
import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class ArrayExpressions {
    public final HashMap<Integer, Expression[]> table;
    private ThreadInfo ti;

    public ArrayExpressions(ThreadInfo ti) {
        table = new HashMap();
        this.ti = ti;
    }

    @Override
    protected ArrayExpressions clone() {
        ArrayExpressions map = new ArrayExpressions(this.ti);
        this.table.forEach((key, value) -> {
            Expression[] newValue = new Expression[value.length];
            for (int i=0; i < value.length; i++)
                newValue[i] = value[i];
            map.add(key, newValue);
        });
        return map;
    }

    public void add(Integer v1, Expression[] v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void update(ArrayRef arrayRef, Expression value) {
        if (!table.containsKey(arrayRef.ref)) {
            table.put(arrayRef.ref, getInitialArrayValues(ti, arrayRef.ref));
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

    public static int getArrayLength(ThreadInfo ti, int ref) {
        ElementInfo eiArray = ti.getElementInfo(ref);
        int len=(eiArray.getArrayFields()).arrayLength(); // assumed concrete
        return len;
    }

    public static Expression[] getInitialArrayValues(ThreadInfo ti, int ref) {
        int len = getArrayLength(ti, ref);
        Expression ret[] = new Expression[len];
        for (int i=0; i < len; i++) {
            ret[i] = getExpression(ti, new ArrayRef(ref, new IntConstant(i))).getFirst();
        }
        return ret;
    }

    public Expression[] lookup(Integer ref) {
        return table.get(ref);
    }

    public void remove(Integer ref) {
        table.remove(ref);
    }
}
