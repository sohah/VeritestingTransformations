package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr.makeNewWalaVarExpr;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion.uniqueCounter;

public class ArrayRef {
    public final int ref;
    public final Expression index;

    public ArrayRef(int ref, Expression index) {
        this.ref = ref;
        this.index = index;
    }

    public static ArrayRef makeArrayRef(ArrayLoadInstruction getIns) {
        if (!(getIns.arrayref instanceof IntConstant))
            throwException(new IllegalArgumentException("cannot make ArrayRef for symbolic array reference"), INSTANTIATION);
        int ref = ((IntConstant)getIns.arrayref).getValue();
        Expression indexName = getIns.index;
        return new ArrayRef(ref, indexName);
    }

    public static ArrayRef makeArrayRef(ArrayStoreInstruction getIns) {
        if (!(getIns.arrayref instanceof IntConstant))
            throwException(new IllegalArgumentException("cannot make ArrayRef for symbolic array reference"), INSTANTIATION);
        int ref = ((IntConstant)getIns.arrayref).getValue();
        Expression indexName = getIns.index;
        return new ArrayRef(ref, indexName);
    }

    public Expression getIndex() {
        return index;
    }

    public int getRef() {
        return ref;
    }

    @Override
    public String toString() {
        return ref+",  "+index;
    }

    @Override
    public boolean equals(Object obj) {
        if (ArrayRef.class.isInstance(obj)) {
            ArrayRef f = (ArrayRef) obj;
            return ref == f.ref && index.equals(f.index);
        }
        else return false;
    }

    @Override
    protected ArrayRef clone() {
        if (index instanceof IntVariable) {
            IntVariable i = (IntVariable) index;
            return new ArrayRef(ref, new IntVariable(i.getName(), i.getLowerBound(), i.getUpperBound()));
        }
        else if (index instanceof IntConstant) {
            return new ArrayRef(ref, new IntConstant(((IntConstant) index).getValue()));
        } else if (index instanceof WalaVarExpr) {
            return new ArrayRef(ref, ((WalaVarExpr)index).clone());
        }  else {
            throwException(new IllegalArgumentException("Unsupported index type found when cloning ArrayRef"), INSTANTIATION);
            return null;
        }
    }

    public static boolean looseArrayRefEquals(ArrayRef arrayRef, ArrayRef key) {
        if (arrayRef.ref == key.ref) {
            boolean bothIntConst = arrayRef.index instanceof IntConstant && key.index instanceof IntConstant;
            if (!bothIntConst || ((IntConstant) arrayRef.index).getValue() == ((IntConstant) key.index).getValue()) {
                return true;
            }
        }
        return false;
    }

    public static Pair<ArrayRef, Stmt> mergeArrayRefs(Expression condition, ArrayRef thenRef, ArrayRef elseRef) throws StaticRegionException {
        ArrayRef ret = (thenRef == null) ^ (elseRef == null) ? (thenRef != null ? thenRef : elseRef) : null;
        if (thenRef == null && elseRef == null) throwException(new StaticRegionException("Cannot merge two null array references"), INSTANTIATION);
        if (thenRef.ref != elseRef.ref) throwException(new StaticRegionException("Cannot merge ArrayRefs for two different arrays"), INSTANTIATION);
        if (ret != null) return new Pair(ret, null);
        // If both refer to the same array location then return one of them
        // Else we need to merge these two refs into one
        if (thenRef.index instanceof IntConstant && elseRef.index instanceof IntConstant) {
            if (((IntConstant) thenRef.index).getValue() == ((IntConstant) elseRef.index).getValue())
                return new Pair(thenRef, null);
        }
        if (thenRef.index instanceof WalaVarExpr && elseRef.index instanceof WalaVarExpr &&
                thenRef.index.equals(elseRef.index)) {
            return new Pair(thenRef, null);
        }
        WalaVarExpr walaVarExpr = makeNewWalaVarExpr(uniqueCounter);
        Stmt assignStmt = new AssignmentStmt(walaVarExpr, new GammaVarExpr(condition, thenRef.index, elseRef.index));
        return new Pair(new ArrayRef(thenRef.ref, walaVarExpr), assignStmt);
    }

}
