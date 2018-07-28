package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.InputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

public class ExprSubstitutionVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private ThreadInfo ti;
    private StackFrame sf;
    public ExprVisitorAdapter eva;
    private StaticRegion staticRegion;
    private SlotTypeTable slotTypeTable;
    private ValueSymbolTable valueSymbolTable;

    public ExprSubstitutionVisitor(ThreadInfo ti, StaticRegion staticRegion, SlotTypeTable slotTypeTable, ValueSymbolTable valueSymbolTable) {
        super();
        this.ti = ti;
        this.sf = ti.getTopFrame();
        eva = super.eva;
        this.staticRegion = staticRegion;
        this.valueSymbolTable = valueSymbolTable;
        this.slotTypeTable = slotTypeTable;
    }

    //SH: An invariant here is that all stackSlots that a var can map to, must all have the same value
    @Override
    public Expression visit(WalaVarExpr expr) {
        InputTable inputTable = staticRegion.inputTable;
        Integer slot = inputTable.lookup(expr.number);
        if (slot != null) {
            gov.nasa.jpf.symbc.numeric.Expression varValue;
            varValue = (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(slot);
            if (varValue == null)
                try {
                    varValue = createConstantForType(slot);
                } catch (StaticRegionException e) {
                    System.out.println(e.getMessage());
                }
            Expression greenValue = SPFToGreenExpr(varValue);
            String type = sf.getLocalVariableType(slot);
            valueSymbolTable.add(expr.number, greenValue);
            slotTypeTable.add(slot, type);
            return greenValue;
        } else { //not a stack slot var, try to check if it is a constant from wala
            SymbolTable symbolTable = staticRegion.ir.getSymbolTable();
            if ((expr.number > -1) && (symbolTable.isConstant(expr.number))) {
                Expression greenValue = makeConstantFromWala(expr);
                valueSymbolTable.add(expr.number, greenValue);
                return greenValue;
            } else{ // it is an intermediate variable, just return it back.
                System.out.println("couldn't infer the type or the value for " + expr.toString());
                return expr;
            }
        }
    }


    private Expression makeConstantFromWala(WalaVarExpr expr) {
        int walaId = expr.number;
        SymbolTable symbolTable = staticRegion.ir.getSymbolTable();
        if (symbolTable.isBooleanConstant(walaId) || symbolTable.isIntegerConstant(walaId))
            return new IntConstant((Integer)symbolTable.getConstantValue(walaId));
        else if (symbolTable.isFloatConstant(walaId) || symbolTable.isDoubleConstant(walaId))
            return new RealConstant((Integer)symbolTable.getConstantValue(walaId));
        else if (symbolTable.isTrue(walaId))
            return new IntConstant(1);
        else if (symbolTable.isFalse(walaId))
            return new IntConstant(0);
        else // is a constant that we don't support, then just return it back.
        {  System.out.println("constant type not supported for " + expr.toString());
            return expr;}

    }

    private gov.nasa.jpf.symbc.numeric.Expression createConstantForType(int variableSlot) throws StaticRegionException {
        String varType = sf.getLocalVariableType(variableSlot);
        if (varType != null) {
            switch (varType) {
                case "double":
                case "float":
                case "long":
                    return new gov.nasa.jpf.symbc.numeric.RealConstant(sf.getLocalVariable(variableSlot));
                case "int":
                case "short":
                case "boolean":
                default: //considered here an object reference
                    return new IntegerConstant(sf.getLocalVariable(variableSlot));
            }
        } else {
            System.out.println("SPF does not know the type, type is assumed int.");
            return new IntegerConstant(sf.getLocalVariable(variableSlot));
        }
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    public static StaticRegionException sre = new StaticRegionException("region substitution problem in ExprSubstitutionVisitor.");


}
