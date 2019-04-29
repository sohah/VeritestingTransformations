package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair;

import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.HashMap;
import java.util.List;

public class SketchSubsVisitor extends AstMapVisitor {

    private HashMap<String, Expr> paramToActualBindMap;

    public SketchSubsVisitor(HashMap<String, Expr> paramToActualBindMap) {
        this.paramToActualBindMap = paramToActualBindMap;
    }


    @Override
    public Expr visit(IdExpr e) { // this is where the substitution takes place.
        Expr actualBinding = paramToActualBindMap.get(e.id);
        boolean isInput = actualBinding != null;
        if (isInput)
            return actualBinding;
        else
            return e;
    }


    public static Ast execute(RepairNode repairNode, HashMap<String, Expr> paramToActualBindMap) {
        assert (paramToActualBindMap != null);
        SketchSubsVisitor mySketchVisitor = new SketchSubsVisitor(paramToActualBindMap);
        return repairNode.accept(mySketchVisitor);
    }

    public static List<Equation> execute(List<Equation> equations, HashMap<String, Expr> paramToActualBindMap) {
        assert (paramToActualBindMap != null);
        SketchSubsVisitor mySketchVisitor = new SketchSubsVisitor(paramToActualBindMap);
        return mySketchVisitor.visitEquations(equations);
    }
}
