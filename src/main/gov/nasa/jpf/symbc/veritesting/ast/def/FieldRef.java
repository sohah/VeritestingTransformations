package gov.nasa.jpf.symbc.veritesting.ast.def;

public class FieldRef {
    public final int ref;
    public final String field;


    public FieldRef(int ref, String field) {
        this.ref = ref;
        this.field = field;
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
}
