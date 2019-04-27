package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import jkind.lustre.BinaryOp;
import jkind.lustre.NamedType;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import za.ac.sun.cs.green.expr.Operation;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.lusterStringType;
import static jkind.lustre.UnaryOp.NEGATIVE;
import static jkind.lustre.UnaryOp.NOT;

public class DiscoveryUtil {
    public static NamedType stringToLusterType(String typeName) {
        if (typeName.equals("int"))
            return lusterIntType;
        else if (typeName.equals("float"))
            return lusterFloatType;
        else if (typeName.equals("bool"))
            return lusterBoolType;
        else if (typeName.equals("string"))
            return lusterStringType;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }


    public static UnaryOp toLustreUnaryOp(Operation.Operator operator) {
        if (operator.toString().equals("-"))
            return NEGATIVE;
        else if (operator.toString().equals("!"))
            return NOT;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static BinaryOp toLustreBinaryOp(Operation.Operator operator) {
        if (operator == Operation.Operator.ADD)
            return BinaryOp.PLUS;
        else if (operator == Operation.Operator.SUB)
            return BinaryOp.MINUS;
        if (operator == Operation.Operator.MUL)
            return BinaryOp.MULTIPLY;
        else if (operator == Operation.Operator.DIV)
            return BinaryOp.DIVIDE;
        else if (operator == Operation.Operator.EQ)
            return BinaryOp.EQUAL;
        else if (operator == Operation.Operator.DIV)
            return BinaryOp.INT_DIVIDE;
        else if (operator == Operation.Operator.NE)
            return BinaryOp.NOTEQUAL;
        else if (operator == Operation.Operator.GT)
            return BinaryOp.GREATER;
        else if (operator== Operation.Operator.LT)
            return BinaryOp.LESS;
        else if (operator == Operation.Operator.GE)
            return BinaryOp.GREATEREQUAL;
        else if (operator == Operation.Operator.LE)
            return BinaryOp.LESSEQUAL;
        else if (operator == Operation.Operator.OR)
            return BinaryOp.OR;
        else if (operator == Operation.Operator.AND)
            return BinaryOp.AND;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }
}
