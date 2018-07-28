package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.numeric.GreenToSPFTranslator;
import gov.nasa.jpf.symbc.numeric.solvers.SolverTranslator;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntVariable;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.RealVariable;

public class ExprUtil {

    public static Expression SPFToGreenExpr(gov.nasa.jpf.symbc.numeric.Expression spfExp) {
        SolverTranslator.Translator toGreenTranslator = new SolverTranslator.Translator();
        spfExp.accept(toGreenTranslator);
        return toGreenTranslator.getExpression();
    }


    public static String AstToString(Expression expression) {
        if (expression instanceof Operation) {
            Operation operation = (Operation) expression;
            String str = "";
            if (operation.getOperator().getArity() == 2)
                str = "(" + AstToString(operation.getOperand(0)) + " " + operation.getOperator().toString() + " " +
                        AstToString(operation.getOperand(1)) + ")";
            else if (operation.getOperator().getArity() == 1)
                str = "(" + operation.getOperator().toString() + AstToString(operation.getOperand(0)) + ")";
            return str;
        } else
            return expression.toString();
    }

    public static gov.nasa.jpf.symbc.numeric.Expression greenToSPFExpression(Expression greenExpression) {
        GreenToSPFTranslator toSPFTranslator = new GreenToSPFTranslator();
        return toSPFTranslator.translate(greenExpression);
    }


    public static Expression createGreenVar(String type, String varId) {
            switch (type) {
                case "double":
                case "float":
                case "long":
                    return new RealVariable(varId, Double.MIN_VALUE, Double.MAX_VALUE);
                case "int":
                case "short":
                case "boolean":
                default: //considered here an object reference
                    return new IntVariable(varId, Integer.MIN_VALUE, Integer.MAX_VALUE);
            }
        }
    }
