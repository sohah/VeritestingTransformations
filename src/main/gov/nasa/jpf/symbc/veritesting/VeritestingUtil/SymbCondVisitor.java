package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import ia_parser.Exp;
import za.ac.sun.cs.green.expr.*;

public class SymbCondVisitor implements ExprVisitor<Expression> {
    private boolean isSymCondition = false;
    private SlotParamTable slotParamTable;
    private StackFrame sf;
    public final ExprVisitorAdapter<Expression> eva =
            new ExprVisitorAdapter<Expression>(this);


    public SymbCondVisitor(StackFrame sf, SlotParamTable slotParamTable) {
        this.slotParamTable = slotParamTable;
        this.sf = sf;
    }

    public Expression visit(WalaVarExpr expr) {
        if (!isSymCondition) {
            int[] slots = slotParamTable.lookup(expr.number);
            int slot;
            if (slots != null){
                slot = slots[0];
                gov.nasa.jpf.symbc.numeric.Expression operand = (gov.nasa.jpf.symbc.numeric.Expression)
                        sf.getSlotAttr(slot);
                if (operand != null)
                    isSymCondition = true;
            }
        }
        return null;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return null;
    }

    @Override
    public Expression visit(GammaVarExpr expr) {
        return null;
    }

    @Override
    public Expression visit(IntConstant expr) {
        return null;
    }

    @Override
    public Expression visit(IntVariable expr) {
        return null;
    }


    @Override
    public Expression visit(Operation expr) {
        Expression [] operands = new Expression [expr.getArity()];
        int index = 0;
        for (Expression e: expr.getOperands()) {
            operands[index++] = eva.accept(e);
        }
        return null;
    }

    @Override
    public Expression visit(RealConstant expr) {
        return null;
    }

    @Override
    public Expression visit(RealVariable expr) {
        return null;
    }

    @Override
    public Expression visit(StringConstantGreen expr) {
        return null;
    }

    @Override
    public Expression visit(StringVariable expr) {
        return null;
    }

    @Override
    public Expression visit(IfThenElseExpr expr) {
        eva.accept(expr.condition);
        return null;
    }

    public boolean isSymCondition() {
        return isSymCondition;
    }
}
