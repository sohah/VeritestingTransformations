package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.IntConstant;
/**
 * This class is used to represent field-reference pair that is used in RangerIR to provide SSA for fields.
 */

public class FieldRef {
    public final int ref;
    public final String field;
    public final boolean isStatic;
    public final String className;


    public FieldRef(int ref, String className, String field, boolean isStatic) {
        this.ref = ref;
        this.field = field;
        this.isStatic = isStatic;
        this.className = className;
    }

    public static FieldRef makeGetFieldRef(ThreadInfo ti, GetInstruction getIns) throws StaticRegionException {
        if (!(getIns.ref instanceof IntConstant) && !getIns.getOriginal().isStatic())
            throw new IllegalArgumentException("cannot make FieldRef for symbolic object reference");
        // getIns.ref contains object reference whereas putIns.def contains object reference
        int ref = getIns.getOriginal().isStatic() ? -1 : ((IntConstant)getIns.ref).getValue();
        if (ref == 0) throw new StaticRegionException("Cannot get any information from null objects");
        String fieldName = getIns.field.getName().toString();
        String className = getIns.getOriginal().isStatic() ?
                getIns.field.getDeclaringClass().getName().getClassName().toString():
                ti.getClassInfo(ref).getName();
        return new FieldRef(ref, className, fieldName, getIns.getOriginal().isStatic());
    }

    public static FieldRef makePutFieldRef(ThreadInfo ti, PutInstruction putIns) throws StaticRegionException {
        if (!(putIns.def instanceof IntConstant)&& !putIns.getOriginal().isStatic())
            throw new IllegalArgumentException("cannot make FieldRef for symbolic object reference");
        int ref = putIns.getOriginal().isStatic() ? -1 : ((IntConstant)putIns.def).getValue();
        if (ref == 0) throw new StaticRegionException("Cannot get any information from null objects");
        String fieldName = putIns.field.getName().toString();
        String className = putIns.getOriginal().isStatic() ?
                putIns.field.getDeclaringClass().getName().getClassName().toString():
                ti.getClassInfo(ref).getName();
        return new FieldRef(ref, className, fieldName, putIns.getOriginal().isStatic());
    }

    public String getField() {
        return field;
    }

    public int getRef() {
        return ref;
    }

    @Override
    public String toString() {
        return ref+",  "+field;
    }

    @Override
    public boolean equals(Object obj) {
        if (FieldRef.class.isInstance(obj)) {
            FieldRef f = (FieldRef) obj;
            return ref == f.ref && field.equals(f.field);
        }
        else return false;
    }

    @Override
    protected FieldRef clone() {
        return new FieldRef(ref, className, field, isStatic);
    }
}
