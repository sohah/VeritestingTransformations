package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class FieldReferenceVar implements Var{
    private  FieldReference fieldReference;
    private  int subscript;

    public FieldReferenceVar(FieldReference fieldReference, int subscript) {
        this.fieldReference = fieldReference;
        this.subscript = subscript;
    }


    public FieldReference getFieldReference() {
        return fieldReference;
    }

    public int getSubscript() {
        return subscript;
    }

    public void setFieldReference(FieldReference fieldReference) {
        this.fieldReference = fieldReference;
    }

    public void setSubscript(int subscript) {
        this.subscript = subscript;
    }

    @Override
    public Var getVar() {
        return this;
    }

    @Override
    public void setVar(Var fieldRefVar) {
        this.fieldReference = ((FieldReferenceVar)fieldRefVar).fieldReference;
        this.subscript = ((FieldReferenceVar)fieldRefVar).subscript;
    }

    @Override
    public String toString() {
        return "("+this.fieldReference.toString() +"," + this.subscript +")";
    }
}
