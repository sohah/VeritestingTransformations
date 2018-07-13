package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class FieldReference {
    private int ref;
    private String field;


    public FieldReference(int ref, String field) {
        this.ref = ref;
        this.field = field;
    }

    public String getField() {
        return field;
    }

    public int getRef() {
        return ref;
    }


    public void setField(String field) {
        this.field = field;
    }

    public void setRef(int ref) {
        this.ref = ref;
    }

    @Override
    public String toString() {
        return ref+","+field;
    }
}
