package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.SymbolTable;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.ValueSymbolTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution.VarTypeTable;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;

enum DefUseVisit {DEF, USE};

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
                if (defUseVisit == DefUseVisit.USE)
                    seenVars.add(expr.number);
                else
                    inputTable.remove(expr.number);

        return expr;
    }
}
