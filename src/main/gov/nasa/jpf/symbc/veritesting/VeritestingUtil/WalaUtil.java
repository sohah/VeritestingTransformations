package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.RealConstant;

public class WalaUtil {


    public static Expression makeConstantFromWala(SymbolTable symbolTable, int walaId) {

        if (symbolTable.isBooleanConstant(walaId) || symbolTable.isIntegerConstant(walaId))
            return new IntConstant((Integer) symbolTable.getConstantValue(walaId));
        else if (symbolTable.isFloatConstant(walaId) || symbolTable.isDoubleConstant(walaId))
            return new RealConstant((Double) symbolTable.getConstantValue(walaId));
        else if (symbolTable.isTrue(walaId))
            return new IntConstant(1);
        else if (symbolTable.isFalse(walaId))
            return new IntConstant(0);
        else // is a constant that we don't support, then just return it back.
        {
            System.out.println("constant type not supported for @w" + walaId);
            return null;
        }

    }
}
