package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.CompositionStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;

import java.io.File;

/**
 * This class provides some utility methods for SPF.
 */
public class SpfUtil {

    private static int operandNum;

    /**
     * Returns number of operands depending on the if-bytecode instruction.
     * @param instruction"if" bytecode instruction
     * @return Number of operands.
     * @throws StaticRegionException
     */
    public static Integer getOperandNumber(String instruction) throws StaticRegionException {
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

    /**
     * Checks if the "if" condition is symbolic based on the the operands of the "if" bytecode instruction.
     * @param sf Current stackfram.
     * @param ins Current "if" bytecode instruction.
     * @return True if the operand(s) of "if" condition is symbolic and false if it was concerete.
     * @throws StaticRegionException
     */
    public static boolean isSymCond(StackFrame sf, Instruction ins) throws StaticRegionException {
        boolean isSymCondition = false;
        SpfUtil.getOperandNumber(ins.getMnemonic());
        if (operandNum == 1) {
            gov.nasa.jpf.symbc.numeric.Expression operand1 = (gov.nasa.jpf.symbc.numeric.Expression)
                    sf.getOperandAttr();
            if (operand1 != null)
                isSymCondition = true;
        }
        if (operandNum == 2) {
            IntegerExpression operand1 = (IntegerExpression) sf.getOperandAttr(1);
            if (operand1 != null)
                isSymCondition = true;
            IntegerExpression operand2 = (IntegerExpression) sf.getOperandAttr(0);
            if (operand2 != null)
                isSymCondition = true;
        }
        return isSymCondition;
    }

    /**
     * Checks if the "if" condition is symbolic by visiting the condition expression of the statement of the staticRegion
     * @param sf Current stack frame.
     * @param slotParamTable Environment table that is holding var to slot mapping.
     * @param stmt Statement of the static region.
     * @return True if the operand(s) of "if" condition is symbolic and false if it was concerete.
     * @throws StaticRegionException
     */
    public static boolean isSymCond(StackFrame sf, SlotParamTable slotParamTable, Stmt stmt) throws StaticRegionException {

        SymbCondVisitor symbCondVisitor = new SymbCondVisitor(sf, slotParamTable);
        ExprVisitorAdapter eva = symbCondVisitor.eva;
        if(stmt instanceof CompositionStmt){
            eva.accept(((IfThenElseStmt)((CompositionStmt) stmt).s1).condition);
        }
        else if(stmt instanceof IfThenElseStmt)
            eva.accept(((IfThenElseStmt) stmt).condition);
        else
            throw new StaticRegionException("Cant veritesting a region that does not start with if condition");
        return symbCondVisitor.isSymCondition();
    }

    /**
     * This creates SPF constants depending on the type of the variable.
     * @param sf Current Stack Frame
     * @param variable Variable number for which we want to create the constant.
     * @param varType The type of which the constant should be created in SPF.
     * @return SPF constant expression..
     * @throws StaticRegionException
     */
    public static gov.nasa.jpf.symbc.numeric.Expression createSPFVariableForType(StackFrame sf, int variable, String varType) throws StaticRegionException {
        if (varType != null) {
            switch (varType) {
                case "double":
                case "float":
                case "long":
                    return new gov.nasa.jpf.symbc.numeric.RealConstant(variable);
                case "int":
                case "short":
                case "boolean":
                default: //considered here an object reference
                    return new IntegerConstant(variable);
            }
        } else {
            System.out.println("SPF does not know the type, type is assumed int.");
            return new IntegerConstant(variable);
        }
    }


    public static void emptyFolder(File folder) {
        File[] files = folder.listFiles();
        if(files!=null) { //some JVMs return null for empty dirs
            for(File f: files) {
                if(f.isDirectory()) {
                    emptyFolder(f);
                } else {
                    f.delete();
                }
            }
        }
    }



    public static Comparator getComparator(Instruction instruction) {
        switch (instruction.getMnemonic()) {
            case "ifeq":
            case "if_icmpeq":
                return Comparator.EQ;
            case "ifge":
            case "if_icmpge":
                return Comparator.GE;
            case "ifle":
            case "if_icmple":
                return Comparator.LE;
            case "ifgt":
            case "if_icmpgt":
                return Comparator.GT;
            case "iflt":
            case "if_icmplt":
                return Comparator.LT;
            case "ifne":
            case "if_icmpne":
                return Comparator.NE;
            default:
                System.out.println("Unknown comparator: " + instruction.getMnemonic());
                assert(false);
                return null;
        }
    }

    public static Comparator getNegComparator(Instruction instruction) {
        switch (instruction.getMnemonic()) {
            case "ifeq":
            case "if_icmpeq":
                return Comparator.NE;
            case "ifge":
            case "if_icmpge":
                return Comparator.LT;
            case "ifle":
            case "if_icmple":
                return Comparator.GT;
            case "ifgt":
            case "if_icmpgt":
                return Comparator.LE;
            case "iflt":
            case "if_icmplt":
                return Comparator.GE;
            case "ifne":
            case "if_icmpne":
                return Comparator.EQ;
            default:
                System.out.println("Unknown comparator: " + instruction.getMnemonic());
                assert(false);
                return null;
        }
    }

}
