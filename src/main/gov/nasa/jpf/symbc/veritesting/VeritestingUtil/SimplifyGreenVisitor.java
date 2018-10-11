package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import za.ac.sun.cs.green.expr.*;

public class SimplifyGreenVisitor extends Visitor {

    public Expression returnExp;

    @Override
    public void postVisit(Operation operation) throws VisitorException {

        Expression e1, e2;

        switch (operation.getOperator()) {
            case AND:
                operation.getOperand(0).accept(this);
                e1 = returnExp;
                operation.getOperand(1).accept(this);
                e2 = returnExp;

                if ((e1 == Operation.FALSE) || (e1 == Operation.FALSE))
                    returnExp = Operation.FALSE;
                else if (e1 == Operation.TRUE)
                    returnExp = e2;
                else if (e2 == Operation.TRUE)
                    returnExp = e1;
                else returnExp = new Operation(Operation.Operator.AND, e1, e2);
                break;

            case OR:
                operation.getOperand(0).accept(this);
                e1 = returnExp;
                operation.getOperand(1).accept(this);
                e2 = returnExp;

                if ((e1 == Operation.TRUE) || (e1 == Operation.TRUE))
                    returnExp = Operation.TRUE;
                else if (e1 == Operation.FALSE)
                    returnExp = e2;
                if (e2 == Operation.FALSE)
                    returnExp = e1;
                else
                    returnExp = new Operation(Operation.Operator.OR, e1, e2);
                break;

            case NOT:
                operation.getOperand(0).accept(this);
                e1 = returnExp;

                if (e1 == Operation.TRUE)
                    returnExp = Operation.FALSE;
                else if (e1 == Operation.FALSE)
                    returnExp = Operation.TRUE;
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.NOT))
                    returnExp = ((Operation) e1).getOperand(0);
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.EQ))
                    returnExp = new Operation(Operation.Operator.NE, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.NE))
                    returnExp = new Operation(Operation.Operator.EQ, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.GT))
                    returnExp = new Operation(Operation.Operator.LE, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.GE))
                    returnExp = new Operation(Operation.Operator.LT, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.LE))
                    returnExp = new Operation(Operation.Operator.GT, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
                else if ((e1 instanceof Operation) && (((Operation) e1).getOperator() == Operation.Operator.LT))
                    returnExp = new Operation(Operation.Operator.GE, ((Operation) e1).getOperand(0), ((Operation) e1).getOperand(1));
                else
                    returnExp = new Operation(Operation.Operator.NOT, e1);
                break;
            default:
                returnExp = operation;
                break;
        }
    }
}
