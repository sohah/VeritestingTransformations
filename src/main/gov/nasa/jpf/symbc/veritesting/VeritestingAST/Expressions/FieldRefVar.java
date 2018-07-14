package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class FieldRefVar implements Var{
    private FieldRef fieldRef;
    private  int subscript;

    public FieldRefVar(FieldRef fieldRef, int subscript) {
        this.fieldRef = fieldRef;
        this.subscript = subscript;
    }


    public FieldRef getFieldRef() {
        return fieldRef;
    }

    public int getSubscript() {
        return subscript;
    }

    public void setFieldRef(FieldRef fieldRef) {
        this.fieldRef = fieldRef;
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
        this.fieldRef = ((FieldRefVar)fieldRefVar).fieldRef;
        this.subscript = ((FieldRefVar)fieldRefVar).subscript;
    }

    @Override
    public String toString() {
        return "("+this.fieldRef.toString() +"," + this.subscript +")";
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitFieldReferenceVar(this);
    }
}
