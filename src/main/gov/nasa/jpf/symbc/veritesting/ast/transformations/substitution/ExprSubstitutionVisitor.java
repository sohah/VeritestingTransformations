package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

/**
 * This is the expression visitor class used during substitution that either returns the value of a variable from a symbol table to returns the expression back if it doesn't make to any entry.
 */
public class ExprSubstitutionVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

    private ThreadInfo ti;
    private StackFrame sf;
    public ExprVisitorAdapter eva;
    private StaticRegion staticRegion;
    private ValueSymbolTable valueSymbolTable;

    public ExprSubstitutionVisitor(ThreadInfo ti, StaticRegion staticRegion,
                                   ValueSymbolTable valueSymbolTable) {
        super();
        this.ti = ti;
        this.sf = ti.getTopFrame();
        eva = super.eva;
        this.staticRegion = staticRegion;
        this.valueSymbolTable = valueSymbolTable;
    }


    @Override
    public Expression visit(WalaVarExpr expr) {

        Expression varValue = valueSymbolTable.lookup(expr.number);
        if (varValue != null)
            return varValue;
        else
            return expr;
    }

    @Override
    public Expression visit(FieldRefVarExpr expr) {
        return expr;
    }

    public static StaticRegionException sre = new StaticRegionException("region substitution problem in ExprSubstitutionVisitor.");


}
