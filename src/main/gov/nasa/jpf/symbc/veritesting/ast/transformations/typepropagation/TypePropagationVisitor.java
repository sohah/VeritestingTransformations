package gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation;

import gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StackSlotTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.SlotTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Set;

public class TypePropagationVisitor extends AstMapVisitor {
    private WalaNumTypesTable walaNumTypesTable;
    private ExprVisitorAdapter<Expression> eva;

    public TypePropagationVisitor(StackSlotTable stackSlotTable, SlotTypeTable slotTypeTable,
                                  WalaNumTypesTable walaNumTypesTable) {
        super(new ExprTypeVisitor(walaNumTypesTable));

        this.walaNumTypesTable = walaNumTypesTable;
        slotTypeTable.getKeys().forEach((slot) -> {
            Set<Integer> vars = stackSlotTable.getVarsOfSlot(slot);
            vars.forEach((valueNum) -> {
                walaNumTypesTable.add(valueNum, slotTypeTable.lookup(slot));
            });
        });
        eva = super.eva;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        ((ExprTypeVisitor)exprVisitor).latestType = null;
        eva.accept(a.rhs);
        if (a.lhs instanceof WalaVarExpr) {
            walaNumTypesTable.add(((WalaVarExpr) a.lhs).number, ((ExprTypeVisitor)exprVisitor).latestType);
        }
        return a;
    }

    public static WalaNumTypesTable propagateTypes(DynamicRegion dynRegion) {
        TypePropagationVisitor visitor = new TypePropagationVisitor(dynRegion.stackSlotTable, dynRegion.slotTypeTable,
                dynRegion.walaNumTypesTable);
        dynRegion.dynStmt.accept(visitor);
        return visitor.walaNumTypesTable;
    }
}
