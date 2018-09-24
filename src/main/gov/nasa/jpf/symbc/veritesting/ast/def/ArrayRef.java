package gov.nasa.jpf.symbc.veritesting.ast.def;

import za.ac.sun.cs.green.expr.*;

public class ArrayRef {
    public final int ref;
    public final Expression index;

    public ArrayRef(int ref, Expression index) {
        this.ref = ref;
        this.index = index;
    }

    public static ArrayRef makeArrayRef(ArrayLoadInstruction getIns) {
        if (!(getIns.arrayref instanceof IntConstant))
            throw new IllegalArgumentException("cannot make ArrayRef for symbolic array reference");
        int ref = ((IntConstant)getIns.arrayref).getValue();
        Expression indexName = getIns.index;
        return new ArrayRef(ref, indexName);
    }

    public static ArrayRef makeArrayRef(ArrayStoreInstruction getIns) {
        if (!(getIns.arrayref instanceof IntConstant))
            throw new IllegalArgumentException("cannot make ArrayRef for symbolic array reference");
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
        } else if (index instanceof RealVariable){
            RealVariable r = (RealVariable) index;
            return new ArrayRef(ref, new RealVariable(r.getName(), r.getLowerBound(), r.getUpperBound()));
        } else if (index instanceof RealConstant) {
            return new ArrayRef(ref, new RealConstant(((RealConstant) index).getValue()));
        } else throw new IllegalArgumentException("Unsupported index type found when cloning ArrayRef");
    }
}