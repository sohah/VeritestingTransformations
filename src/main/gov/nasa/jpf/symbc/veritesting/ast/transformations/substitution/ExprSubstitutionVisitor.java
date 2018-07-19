package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

public class ExprSubstitutionVisitor extends ExprMapVisitor {

    private ThreadInfo ti;
    private StackFrame sf;
    private Region region;

    public ExprSubstitutionVisitor(ThreadInfo ti, Region region) {
        super();
        this.ti = ti;
        this.sf = ti.getTopFrame();
        this.region = region;
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        StackSlotTable stackSlotTable = region.getStackSlotTable();
        int[] stackSlots = stackSlotTable.lookup(expr.number);
        if (stackSlots != null) {
            assert(stackSlots.length>0);
            gov.nasa.jpf.symbc.numeric.Expression varValue;
            varValue = (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(stackSlots[0]);
            if (varValue == null)
                varValue = new IntegerConstant(sf.getLocalVariable(stackSlots[0]));
            Expression greenValue = SPFToGreenExpr(varValue);
            region.getValueSymbolTable().add(expr.number, greenValue);
            return greenValue;
        }
        else
            return expr;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }
}
