package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

public final class FieldRefVarExpr extends Variable {
    public final FieldRef fieldRef;
    public final int subscript;

    public FieldRefVarExpr(FieldRef fieldRef, int subscript) {
        super("@r"+fieldRef.ref + "." + fieldRef.field + "#" + subscript);
        this.fieldRef = fieldRef;
        this.subscript = subscript;
    }

    @Override
    public void accept(Visitor visitor) throws VisitorException {
        // will call the Variable entry.
        visitor.preVisit(this);
        visitor.postVisit(this);
        IntVariable v;
    }

    @Override

    // I am making class final so that equality works correctly.
    public boolean equals(Object o) {
        if (o != null && o instanceof FieldRefVarExpr) {
            FieldRefVarExpr other = (FieldRefVarExpr)o;
            return (this.fieldRef.equals(other.fieldRef) &&
                    this.subscript == other.subscript);
        }
        return false;
    }

    @Override
    public String toString() {
        return getName();
    }

    @Override
    public int getLength() {
        return 1;
    }

    @Override
    public int getLeftLength() {
        return 1;
    }

    @Override
    public int numVar() {
        return 1;
    }

    @Override
    public int numVarLeft() {
        return 1;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }

}
