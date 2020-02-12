package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.mutation;

import jkind.lustre.*;
import jkind.lustre.visitors.ExprVisitor;
// this is now pending
public class ExprSize implements ExprVisitor<Integer> {

    @Override
    public Integer visit(ArrayAccessExpr e) {
        assert false; // I am not expecting to see properties that contains that.
        return 1; // size of array access is assumed one, since we can change here only the index of the array.
    }

    @Override
    public Integer visit(ArrayExpr e) {
        //size of an arrayExpr definition is assumed to be the size of its elements.
        assert false; // I am not expecting to see properties that contains that.
        return e.elements.size();
    }

    @Override
    public Integer visit(ArrayUpdateExpr e) {
        System.out.println("currently unsupported property expression");
        assert false;
        return null;
    }

    @Override
    public Integer visit(BinaryExpr e) {
        return null;
    }

    @Override
    public Integer visit(BoolExpr e) {
        return null;
    }

    @Override
    public Integer visit(CastExpr e) {
        return null;
    }

    @Override
    public Integer visit(CondactExpr e) {
        return null;
    }

    @Override
    public Integer visit(FunctionCallExpr e) {
        return null;
    }

    @Override
    public Integer visit(IdExpr e) {
        return null;
    }

    @Override
    public Integer visit(IfThenElseExpr e) {
        return null;
    }

    @Override
    public Integer visit(IntExpr e) {
        return null;
    }

    @Override
    public Integer visit(NodeCallExpr e) {
        return null;
    }

    @Override
    public Integer visit(RepairExpr e) {
        return null;
    }

    @Override
    public Integer visit(RealExpr e) {
        return null;
    }

    @Override
    public Integer visit(RecordAccessExpr e) {
        return null;
    }

    @Override
    public Integer visit(RecordExpr e) {
        return null;
    }

    @Override
    public Integer visit(RecordUpdateExpr e) {
        return null;
    }

    @Override
    public Integer visit(TupleExpr e) {
        return null;
    }

    @Override
    public Integer visit(UnaryExpr e) {
        return null;
    }
}
