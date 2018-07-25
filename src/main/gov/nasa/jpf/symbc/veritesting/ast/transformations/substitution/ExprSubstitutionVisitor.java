package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.InputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
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
    private VarTypeTable varTypeTable;
    private ValueSymbolTable valueSymbolTable;

    public ExprSubstitutionVisitor(ThreadInfo ti, StaticRegion staticRegion, VarTypeTable varTypeTable, ValueSymbolTable valueSymbolTable) {
        super();
        this.ti = ti;
        this.sf = ti.getTopFrame();
        eva = super.eva;
        this.staticRegion = staticRegion;
        this.valueSymbolTable = valueSymbolTable;
        this.varTypeTable = varTypeTable;
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
            varTypeTable.add(expr.number, type);
            return greenValue;
        } else { //not a stack slot var, try to check if it is a constant.
            SymbolTable symbolTable = staticRegion.ir.getSymbolTable();
            if (symbolTable.isConstant(expr.number)) {
                Expression greenValue = makeConstantFromWala(expr.number);
                valueSymbolTable.add(expr.number, greenValue);
                return greenValue;
            } else
                return expr;
        }
    }


    private Expression makeConstantFromWala(int walaId) {
        SymbolTable symbolTable = staticRegion.ir.getSymbolTable();
        if (symbolTable.isBooleanConstant(walaId) ||
                symbolTable.isIntegerConstant(walaId))
            return SPFToGreenExpr(new IntegerConstant((Integer)symbolTable.getConstantValue(walaId)));
        else if (symbolTable.isFloatConstant(walaId) || symbolTable.isDoubleConstant(walaId))
            return SPFToGreenExpr(new gov.nasa.jpf.symbc.numeric.RealConstant((Integer)symbolTable.getConstantValue(walaId)));
        else if (symbolTable.isTrue(walaId))
            return SPFToGreenExpr(new gov.nasa.jpf.symbc.numeric.IntegerConstant(1));
        else if (symbolTable.isFalse(walaId))
            return SPFToGreenExpr(new gov.nasa.jpf.symbc.numeric.IntegerConstant(0));
        else
            try {
                throw sre;
            } catch (StaticRegionException e) {
                System.out.println("Constant type not supported for Veritesting.");
                System.out.println(e.getMessage());
            }
        return null;
    }

    private gov.nasa.jpf.symbc.numeric.Expression createConstantForType(int variableSlot) throws StaticRegionException {
        String varType = sf.getLocalVariableType(variableSlot);
        if (varType != null) { //SH: sometimes SPF does not give the type! we assume it is int
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
