package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repairbuilders;

import jkind.lustre.*;
import jkind.lustre.visitors.ExprMapVisitor;
import java.util.List;

/**
 * computes the cost of an expression relative to another expression or a the maximum cost possible.
 */
public class MaxCostFunction extends ExprMapVisitor {

    private int cost = 0;

    /**
     * computes the maximum cost of some expr, this will be the cost if all its leaf expressions has changed and
     * will also count towards the cost of removing the expression. Intutively it counts the number of subexpressions
     * that exits in an expression.
     */
    static int compute(Expr expr) {
        MaxCostFunction maxCostFunction = new MaxCostFunction();
        expr.accept(maxCostFunction);
        return maxCostFunction.cost;
    }


    @Override
    public Expr visit(ArrayAccessExpr e) {
        return new ArrayAccessExpr(e.location, e.array.accept(this), e.index.accept(this));
    }

    @Override
    public Expr visit(ArrayExpr e) {
        return new ArrayExpr(e.location, visitExprs(e.elements));
    }

    @Override
    public Expr visit(ArrayUpdateExpr e) {
        return new ArrayUpdateExpr(e.location, e.array.accept(this), e.index.accept(this), e.value.accept(this));
    }

    @Override
    public Expr visit(BinaryExpr e) {
        Expr left = e.left.accept(this);
        Expr right = e.right.accept(this);
        if (e.left == left && e.right == right) {
            return e;
        }
        return new BinaryExpr(e.location, left, e.op, right);
    }

    @Override
    public Expr visit(BoolExpr e) {
        ++cost;
        return e;
    }

    @Override
    public Expr visit(CastExpr e) {
        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(CondactExpr e) {
        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(FunctionCallExpr e) { // function call change costs 1.
        ++cost;
        return new FunctionCallExpr(e.location, e.function, e.args);
    }

    @Override
    public Expr visit(IdExpr e) {
        ++cost;
        return e;
    }

    @Override
    public Expr visit(IfThenElseExpr e) { //cost of if-then-else is already computed from sub-expressions.
        Expr cond = e.cond.accept(this);
        Expr thenExpr = e.thenExpr.accept(this);
        Expr elseExpr = e.elseExpr.accept(this);
        if (e.cond == cond && e.thenExpr == thenExpr && e.elseExpr == elseExpr) {
            return e;
        }
        return new IfThenElseExpr(e.location, cond, thenExpr, elseExpr);
    }

    @Override
    public Expr visit(IntExpr e) {
        ++cost;
        return e;
    }

    @Override
    public Expr visit(NodeCallExpr e) { //cost of a nodecall is 1.
        ++cost;
        return new NodeCallExpr(e.location, e.node, e.args);
    }

    @Override
    public Expr visit(RealExpr e) {
        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(RecordAccessExpr e) {

        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(RecordExpr e) {
        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(RecordUpdateExpr e) {
        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(TupleExpr e) {

        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }

    @Override
    public Expr visit(UnaryExpr e) {
        Expr expr = e.expr.accept(this);
        ++cost;
        if (e.expr == expr) {
            return e;
        }
        return new UnaryExpr(e.location, e.op, expr);
    }

    protected List<Expr> visitExprs(List<? extends Expr> es) {
        System.out.println("Unimplemented maximum cost function. Aborting!");
        assert false;
        return null;
    }
}
