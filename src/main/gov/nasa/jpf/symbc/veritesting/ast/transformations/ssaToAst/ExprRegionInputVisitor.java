package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.InputTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;

public class ExprRegionInputVisitor extends ExprMapVisitor implements ExprVisitor<Expression> {

//SH: I do not like how this is implemented, ideally the visit should have the Def/Use flag with every visit, but that required to change base interfaces. I will keep this for now.

    public static DefUseVisit defUseVisit;
    ArrayList seenVars;
    InputTable inputTable;

    public ExprRegionInputVisitor(InputTable inputTable) {
        this.inputTable = inputTable;
        seenVars = new ArrayList();
    }

    @Override
    public Expression visit(WalaVarExpr expr) {
        if (inputTable.lookup(expr.number) != null)
            if (!seenVars.contains(expr.number))
                if ((!inputTable.ir.getSymbolTable().isConstant(expr.number))
                        && (defUseVisit == DefUseVisit.USE))
                    seenVars.add(expr.number);
                else
                    inputTable.remove(expr.number);

        return expr;
    }
}
