package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;

import java.util.List;

public final class GammaVarExpr extends Variable implements VarExpr {
    public final Expression condition;
    public final VarExpr thenExpr;
    public final VarExpr elseExpr;

    public static String name(Expression condition, VarExpr thenExpr, VarExpr elseExpr) {
        return "(Gamma " + condition.toString() + " " + thenExpr.toString() + " " + elseExpr.toString() + ")";
    }

    public GammaVarExpr(Expression condition, VarExpr thenExpr, VarExpr elseExpr) {
        super(name(condition, thenExpr, elseExpr));
        this.condition = condition;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }


    @Override
    public void accept(Visitor visitor) throws VisitorException {
        visitor.preVisit(this);
        visitor.postVisit(this);
    }

    @Override
    // I am making class final so that equality works correctly.
    public boolean equals(Object o) {
        if (o != null && o instanceof GammaVarExpr) {
            GammaVarExpr other = (GammaVarExpr)o;
            return (this.condition.equals(other.condition) &&
                    this.thenExpr.equals(other.thenExpr) &&
                    this.elseExpr.equals(other.elseExpr));
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

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

}
