package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Visitors.ExprVisitor;

public class GammaVarExpr extends Expr implements VarExpr {
    public final Expr condition;
    public final VarExpr var1;
    public final VarExpr var2;


    public GammaVarExpr(Expr condition, VarExpr var1, VarExpr var2) {
        this.condition = condition;
        this.var1 = var1;
        this.var2 = var2;
    }


    @Override
    public String toString() {
        return " GammaVarExpr( " + condition.toString() + ", " + var1.toString() + ", " + var2.toString() +")";

    }

    @Override
    public <T> T accept(ExprVisitor<T> visitor) {
        return visitor.visit(this);
    }

}
