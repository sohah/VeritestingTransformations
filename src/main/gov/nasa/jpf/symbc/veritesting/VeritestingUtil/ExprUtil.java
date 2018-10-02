package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.numeric.GreenToSPFTranslator;
import gov.nasa.jpf.symbc.numeric.solvers.SolverTranslator;
import za.ac.sun.cs.green.expr.*;

/**
 * A utility class that provides some methods from SPF to Green and vise versa.
 */
public class ExprUtil {

    /**
     * Translates an SPF expression to a Green Expression.
     * @param spfExp SPF Expression
     * @return Green Expression.
     */
    public static Expression SPFToGreenExpr(gov.nasa.jpf.symbc.numeric.Expression spfExp) {
        SolverTranslator.Translator toGreenTranslator = new SolverTranslator.Translator();
        spfExp.accept(toGreenTranslator);
        return toGreenTranslator.getExpression();
    }

    /**
     * Pretty print method to print Green expression.
     * @param expression Green expression.
     * @return String of Green Expression.
     */
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

    /**
     * Translates Green Expession to SPF.
     * @param greenExpression A Green expression to be translated to SPF.
     * @return SPF expression.
     */
    public static gov.nasa.jpf.symbc.numeric.Expression greenToSPFExpression(Expression greenExpression) {
        GreenToSPFTranslator toSPFTranslator = new GreenToSPFTranslator();
        return toSPFTranslator.translate(greenExpression);
    }

    /**
     * Creates a Green variable depending on its type.
     * @param type Type of the variable.
     * @param varId Name of the variable.
     * @return A Green variable.
     */
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

    public static boolean isConstant(Expression expr) {
        return  IntConstant.class.isInstance(expr) || RealConstant.class.isInstance(expr);
    }

    public static String getConstantType(Expression expr) {
        assert isConstant(expr);
        if (IntConstant.class.isInstance(expr)) return "int";
        if (RealConstant.class.isInstance(expr)) return "real";
        return null;
    }

}
