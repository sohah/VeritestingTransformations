package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.sketchRepair;

import jkind.lustre.Ast;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.RepairNode;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.HashMap;

public class SketchSubsVisitor extends AstMapVisitor {

    private HashMap<Expr, Expr> paramToActualBindMap;

    public SketchSubsVisitor(HashMap<Expr, Expr> paramToActualBindMap) {
        this.paramToActualBindMap = paramToActualBindMap;
    }


    @Override
    public Expr visit(IdExpr e) { // this is where the substitution takes place.
        Expr actualBinding = paramToActualBindMap.get(e);
        boolean isInput = actualBinding != null;
        if (isInput)
            return actualBinding;
        else
            return e;
    }


    public static Ast execute(RepairNode repairNode, HashMap<Expr, Expr> paramToActualBindMap) {
        assert (paramToActualBindMap != null);
        SketchSubsVisitor mySketchVisitor = new SketchSubsVisitor(paramToActualBindMap);
        return repairNode.accept(mySketchVisitor);
    }
}
