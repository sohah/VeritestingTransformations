package gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation;

import gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticEnvironment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticEnvironment.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DynamicEnvironment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.DynamicEnvironment.SlotTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Set;

public class TypePropagationVisitor extends AstMapVisitor {
    private VarTypeTable varTypeTable;
    private ExprVisitorAdapter<Expression> eva;

    public TypePropagationVisitor(SlotParamTable slotParamTable, SlotTypeTable slotTypeTable,
                                  VarTypeTable varTypeTable) {
        super(new ExprTypeVisitor(varTypeTable));

        this.varTypeTable = varTypeTable;
        slotTypeTable.getKeys().forEach((slot) -> {
            Set<Integer> vars = slotParamTable.getVarsOfSlot(slot);
            vars.forEach((valueNum) -> {
                varTypeTable.add(valueNum, slotTypeTable.lookup(slot));
            });
        });
        eva = super.eva;
    }

    @Override
    public Stmt visit(AssignmentStmt a) {
        ((ExprTypeVisitor)exprVisitor).latestType = null;
        eva.accept(a.rhs);
        if (a.lhs instanceof WalaVarExpr) {
            varTypeTable.add(((WalaVarExpr) a.lhs).number, ((ExprTypeVisitor)exprVisitor).latestType);
        }
        return a;
    }

    public static VarTypeTable propagateTypes(DynamicRegion dynRegion) {
        TypePropagationVisitor visitor = new TypePropagationVisitor(dynRegion.slotParamTable, dynRegion.slotTypeTable,
                dynRegion.varTypeTable);
        dynRegion.dynStmt.accept(visitor);
        return visitor.varTypeTable;
    }
}
