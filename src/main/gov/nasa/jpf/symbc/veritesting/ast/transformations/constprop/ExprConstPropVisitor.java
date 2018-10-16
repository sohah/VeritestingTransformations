package gov.nasa.jpf.symbc.veritesting.ast.transformations.constprop;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isConstant;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.isSatExpression;

public class ExprConstPropVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private DynamicTable<Expression> constantsTable;
    public StaticRegionException sre = null;

    public ExprConstPropVisitor(DynamicTable<Expression> constantsTable) {
        super();
        eva = super.eva;
        this.constantsTable = constantsTable;
    }

    private Expression lookup(Expression expr) {
        if (constantsTable.lookup((Variable) expr) != null)
            return constantsTable.lookup((Variable) expr);
        else return expr;
    }


    @Override
    public Expression visit(WalaVarExpr expr) {
        return lookup(expr);
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return lookup(expr);
    }

    @Override
    public Expression visit(IntVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(RealVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(StringVariable expr) { return lookup(expr); }

    @Override
    public Expression visit(AstVarExpr expr) { return lookup(expr); }

    @Override
    public Expression visit(ArrayRefVarExpr expr) { return lookup(expr); }

    @Override
    public Expression visit(Operation expr) {
        Expression ret = null;
        Expression op1 = null, op2 = null;
        //TODO: visit operands to populate ret, get op1 and op2 from ret at this point

        if (expr.getArity() == 1) {
            op1 = expr.getOperand(0);
        }
        if (expr.getArity() == 2) {
            op1 = expr.getOperand(0);
            op2 = expr.getOperand(1);
        }
        //TODO: constant-fold these in when possible by first extracting a method out of ExprUtil.isSatExpression and use the extracted method
        switch (expr.getOperator()) {
            case EQ:
            case NE:
            case LT:
            case LE:
            case GT:
            case GE:
            case AND:
            case OR:
            case NOT:
                ExprUtil.SatResult result = isSatExpression(expr);
                ret =  result == ExprUtil.SatResult.TRUE ? new IntConstant(1) :
                        (result == ExprUtil.SatResult.FALSE ? new IntConstant(0): null);
                break;
            case ADD:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() + ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() + ((RealConstant) op2).getValue());
                }
                break;
            case SUB:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() - ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() - ((RealConstant) op2).getValue());
                }
                break;
            case MUL:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() * ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() * ((RealConstant) op2).getValue());
                }
                break;
            case DIV:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() / ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() / ((RealConstant) op2).getValue());
                }
                break;
            case MOD:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() % ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    ret = new RealConstant(((RealConstant) op1).getValue() % ((RealConstant) op2).getValue());
                }
                break;
            case NEG:
                if (op1 instanceof IntConstant) {
                    ret = new IntConstant(-((IntConstant) op1).getValue());
                } else if (op1 instanceof RealConstant) {
                    ret = new RealConstant(-((RealConstant) op1).getValue());
                }
                break;
            case BIT_AND:
                if (op1 instanceof IntConstant && op2 instanceof IntConstant) {
                    ret = new IntConstant(((IntConstant) op1).getValue() & ((IntConstant) op2).getValue());
                } else if (op1 instanceof RealConstant && op2 instanceof RealConstant) {
                    sre = new StaticRegionException("Cannot apply BIT_AND to RealConstant operands");
                }
                break;
            case BIT_OR:
                break;
            case BIT_XOR:
                break;
            case BIT_NOT:
                break;
            case SHIFTL:
                break;
            case SHIFTR:
                break;
            case SHIFTUR:
                break;
            case BIT_CONCAT:
                break;
            case SIN:
                break;
            case COS:
                break;
            case TAN:
                break;
            case ASIN:
                break;
            case ACOS:
                break;
            case ATAN:
                break;
            case ATAN2:
                break;
            case ROUND:
                break;
            case LOG:
                break;
            case EXP:
                break;
            case POWER:
                break;
            case SQRT:
                break;
            default:
                ret = null;
        }
        return ret;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        // TODO: constant-fold gammas when possible
//        return super.visit(expr);
        return expr;
    }
}
