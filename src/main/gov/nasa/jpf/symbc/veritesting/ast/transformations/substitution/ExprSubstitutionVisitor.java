package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.string.StringConstant;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
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
    private DynamicRegion dynRegion;
    public ExprVisitorAdapter eva;

    public ExprSubstitutionVisitor(ThreadInfo ti, DynamicRegion dynRegion) {
        super();
        this.ti = ti;
        this.sf = ti.getTopFrame();
        this.dynRegion = dynRegion;
        eva = super.eva;
    }

    //SH: An invariant here is that all stackSlots that a var can map to, must all have the same value
    @Override
    public Expression visit(WalaVarExpr expr) {
        StackSlotTable stackSlotTable = dynRegion.getStackSlotTable();
        int[] stackSlots = stackSlotTable.lookup(expr.number);
        if (stackSlots != null) {
            assert (stackSlots.length > 0);
            gov.nasa.jpf.symbc.numeric.Expression varValue;
            varValue = (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(stackSlots[0]);
            if (varValue == null)
                try {
                    varValue = createConstantForType(stackSlots[0]);
                } catch (StaticRegionException e) {
                    System.out.println(e.getMessage());
                }
            Expression greenValue = SPFToGreenExpr(varValue);
            String type = sf.getLocalVariableType(stackSlots[0]);
            dynRegion.getValueSymbolTable().add(expr.number, greenValue);
            dynRegion.getVarTypeTable().add(expr.number, type);
            return greenValue;
        } else
            return expr;
    }

    private gov.nasa.jpf.symbc.numeric.Expression createConstantForType(int variableSlot) throws StaticRegionException {
        switch (sf.getLocalVariableType(variableSlot)) {
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
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    public static StaticRegionException sre = new StaticRegionException("region substitution problem in ExprSubstitutionVisitor.");


}
