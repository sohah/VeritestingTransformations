package gov.nasa.jpf.symbc.veritesting.ast.def;

import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

public final class WalaVarExpr extends Variable {

    public final int number;

    public WalaVarExpr(int var) {
        super("@w" + var);
        this.number = var;
    }


    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (o != null && o instanceof WalaVarExpr) {
            WalaVarExpr other = (WalaVarExpr)o;
            return this.number == other.number;
        }
        return false;
    }

    @Override
    public String toString() {
        return getName();
    }

    @Override
    public int getLength() {
        return 0;
    }

    @Override
    public int getLeftLength() {
        return 0;
    }

    @Override
    public int numVar() {
        return 0;
    }

    @Override
    public int numVarLeft() {
        return 0;
    }

    @Override
    public List<String> getOperationVector() {
        return null;
    }
}
