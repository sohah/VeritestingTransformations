package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.vm.StackFrame;

public class SpfUtil {

    private static int operandNum;

    public static Integer operandNumber(String instruction) throws StaticRegionException {
        switch (instruction) {
            case "ifeq":
            case "ifne":
            case "iflt":
            case "ifle":
            case "ifgt":
            case "ifge":
            case "ifnull":
            case "ifnonnull":
                operandNum = 1;
                break;
            case "if_icmpeq":
            case "if_icmpne":
            case "if_icmpgt":
            case "if_icmpge":
            case "if_icmple":
            case "if_icmplt":
                operandNum = 2;
                break;
            default:
                throw new StaticRegionException("Problem finding number of operands for the condition for " + instruction);
        }
        return operandNum;

    }

    public static boolean isConcerteCond(StackFrame sf) {
        boolean isConcreteCondition = true;
        if (operandNum == 1) {
            gov.nasa.jpf.symbc.numeric.Expression operand1 = (gov.nasa.jpf.symbc.numeric.Expression)
                    sf.getOperandAttr();
            if (operand1 != null)
                isConcreteCondition = false;
        }
        if (operandNum == 2) {
            IntegerExpression operand1 = (IntegerExpression) sf.getOperandAttr(1);
            if (operand1 != null)
                isConcreteCondition = false;
            IntegerExpression operand2 = (IntegerExpression) sf.getOperandAttr(0);
            if (operand2 != null)
                isConcreteCondition = false;
        }
        return isConcreteCondition;
    }
}
