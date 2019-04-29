package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair;

import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.math.BigInteger;

public class PartialEvalVisitor extends AstMapVisitor {


    @Override
    public Expr visit(BinaryExpr e) {
        Expr left = e.left.accept(this);
        Expr right = e.right.accept(this);
        if (((left instanceof IntExpr) && (right instanceof IntExpr)) ||
                ((left instanceof BoolExpr) && (right instanceof BoolExpr))) {
            Expr newVal = evalBinaryOp(left, right, e.op);
            if (newVal != null)
                return newVal;
            else //case where we could not do partial evaluation for any reason, we just propagate the binary expr.
                return new BinaryExpr(e.location, left, e.op, right);
        }

        if (e.left == left && e.right == right) {
            return e;
        }
        return new BinaryExpr(e.location, left, e.op, right);
    }

    private Expr evalBinaryOp(Expr left, Expr right, BinaryOp op) {
        BigInteger intVal;
        boolean boolVal;
        if ((left instanceof IntExpr) && (right instanceof IntExpr)) {
            switch (op) {
                case PLUS:
                    intVal = ((IntExpr) left).value.add(((IntExpr) right).value);
                    return new IntExpr(intVal);
                case MINUS:
                    intVal = ((IntExpr) left).value.subtract(((IntExpr) right).value);
                    return new IntExpr(intVal);
                case MULTIPLY:
                    intVal = ((IntExpr) left).value.multiply(((IntExpr) right).value);
                    return new IntExpr(intVal);
                case DIVIDE:
                    intVal = ((IntExpr) left).value.divide(((IntExpr) right).value);
                    return new IntExpr(intVal);
                case INT_DIVIDE:
                    int val2 = ((IntExpr) left).value.intValue() / (((IntExpr) right).value).intValue();
                    return new IntExpr(val2);
                case MODULUS:
                    intVal = ((IntExpr) left).value.mod(((IntExpr) right).value);
                    return new IntExpr(intVal);
                case EQUAL:
                    boolVal = ((IntExpr) left).value.compareTo(((IntExpr) right).value) == 0;
                    return new BoolExpr(boolVal);
                case NOTEQUAL:
                    boolVal = ((IntExpr) left).value.compareTo(((IntExpr) right).value) != 0;
                    return new BoolExpr(boolVal);
                case GREATER:
                    boolVal = ((IntExpr) left).value.compareTo(((IntExpr) right).value) == 1;
                    return new BoolExpr(boolVal);
                case LESS:
                    boolVal = ((IntExpr) left).value.compareTo(((IntExpr) right).value) == -1;
                    return new BoolExpr(boolVal);
                case GREATEREQUAL:
                    boolVal = (((IntExpr) left).value.compareTo(((IntExpr) right).value) == 0)
                            || (((IntExpr) left).value.compareTo(((IntExpr) right).value) == 1);
                    return new BoolExpr(boolVal);
                case LESSEQUAL:
                    boolVal = (((IntExpr) left).value.compareTo(((IntExpr) right).value) == 0)
                            || (((IntExpr) left).value.compareTo(((IntExpr) right).value) == -11);
                    return new BoolExpr(boolVal);
                case OR:
                case AND:
                case XOR:
                case IMPLIES:
                case ARROW:
                    assert false;
                    return null;
            }
        } else {
            assert ((left instanceof BoolExpr) && (right instanceof BoolExpr));
            switch (op) {
                case PLUS:
                case MINUS:
                case MULTIPLY:
                case DIVIDE:
                case INT_DIVIDE:
                case MODULUS:
                    assert false;
                    return null;
                case EQUAL:
                    boolVal = ((BoolExpr) left).value == ((BoolExpr) right).value;
                    return new BoolExpr(boolVal);
                case NOTEQUAL:
                    boolVal = ((BoolExpr) left).value != ((BoolExpr) right).value;
                    return new BoolExpr(boolVal);
                case GREATER:
                case LESS:
                case GREATEREQUAL:
                case LESSEQUAL:
                    assert false;
                    return null;
                case OR:
                    boolVal = ((BoolExpr) left).value || ((BoolExpr) right).value;
                    return new BoolExpr(boolVal);
                case AND:
                    boolVal = ((BoolExpr) left).value && ((BoolExpr) right).value;
                    return new BoolExpr(boolVal);
                case XOR:
                    boolVal = ((BoolExpr) left).value ^ ((BoolExpr) right).value;
                    return new BoolExpr(boolVal);
                case IMPLIES:
                    boolVal = (!((BoolExpr) left).value) || ((BoolExpr) right).value;
                    return new BoolExpr(boolVal);
                case ARROW:
                    System.out.println("undefined reduction during partial evaluation.");
                    return null;
            }
        }
        return null;
    }


    @Override
    public Expr visit(UnaryExpr e) {
        Expr expr = e.expr.accept(this);
        if (expr instanceof BoolExpr) { //only try to do partial evaluation if it happens to be a bool expression.
            Expr newVal = evalUnaryOp(e);
            if (newVal != null)
                return newVal;
            else
                return new UnaryExpr(e.location, e.op, expr);
        }

        if (e.expr == expr) {
            return e;
        }
        return new UnaryExpr(e.location, e.op, expr);
    }

    private Expr evalUnaryOp(UnaryExpr e) {
        assert (e.expr instanceof BoolExpr);
        switch (e.op) {
            case NEGATIVE:
                return null;
            case NOT:
                return new BoolExpr(!((BoolExpr) e.expr).value);
            case PRE:
                return null;
        }
        return null;
    }


    @Override
    public Expr visit(IfThenElseExpr e) {
        Expr cond = e.cond.accept(this);
        if (cond instanceof BoolExpr)
            if (((BoolExpr) cond).value)
                return e.thenExpr.accept(this);
            else
                return e.elseExpr.accept(this);
        else {
            Expr thenExpr = e.thenExpr.accept(this);
            Expr elseExpr = e.elseExpr.accept(this);
            if (e.cond == cond && e.thenExpr == thenExpr && e.elseExpr == elseExpr)
                return e;
            else
                return new IfThenElseExpr(e.location, cond, thenExpr, elseExpr);
        }
    }


    public static Ast execute(Ast repairNodeBinded) {
        return repairNodeBinded.accept(new PartialEvalVisitor());

    }
}
