package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.InputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;

public class ExprRegionInputVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

//SH: visiting all use vars to collect a possible first use for every stack slot.

    private ArrayList seenSlots;
    private InputTable inputTable;
    private SlotParamTable slotParamTable;
    public DefUseVisit defUseVisit;

    public ExprRegionInputVisitor(InputTable inputTable, SlotParamTable slotParamTable) {
        this.inputTable = inputTable;
        this.slotParamTable = slotParamTable;
        this.seenSlots = new ArrayList();
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        int[] varSlots = slotParamTable.lookup(expr.number);
        if (varSlots != null) {
            for (int i = 0; i < varSlots.length; i++)
                if (!seenSlots.contains(varSlots[i])) {
                    if (defUseVisit == DefUseVisit.USE)
                        inputTable.add(expr.number, varSlots[i]);
                    seenSlots.add(varSlots[i]);
                }
        }
        return expr;
    }

}
