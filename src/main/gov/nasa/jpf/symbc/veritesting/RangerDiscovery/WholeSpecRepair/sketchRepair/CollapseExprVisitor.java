package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.sketchRepair;

import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class CollapseExprVisitor extends AstMapVisitor {

    List<Equation> repairNodeEqs;

    HashMap<Expr, Expr> reducedDefinitions = new HashMap<>();

    HashSet<Expr> binds;

    public CollapseExprVisitor(List<Equation> equations, Collection<Expr> binds) {
        this.repairNodeEqs = equations;
        this.binds = (HashSet<Expr>) binds;
    }

    @Override
    public Expr visit(IdExpr e) {
        if (!binds.contains(e)) { //not an input, then try to find its collapsed definition
            Expr collapsedRhsExpr = reducedDefinitions.get(e);
            if (collapsedRhsExpr != null)
                return collapsedRhsExpr;
            else {
                Expr rhsExpr = findEqRhs(e);
                if (rhsExpr == null) {
                    System.out.println("unexpected behaviour, Expr should be defined somewhere. Aborting.");
                    assert false;
                }
                Expr rhsCollapsedExpr = rhsExpr.accept(this);
                reducedDefinitions.put(e, rhsCollapsedExpr);
                return rhsCollapsedExpr;
            }
        }
        return e;
    }

    public static Expr execute(Ast partEvalNode, Collection<Expr> binds) {
        assert (partEvalNode instanceof RepairNode);

        List<Equation> equations = ((RepairNode) partEvalNode).equations;
        Expr outputExpr = selectOutputEq((RepairNode) partEvalNode);

        assert outputExpr != null;

        CollapseExprVisitor collapseExprVisitor = new CollapseExprVisitor(equations, binds);

        return outputExpr.accept(collapseExprVisitor);
    }

    private static Expr selectOutputEq(RepairNode partEvalNode) {
        if (partEvalNode.outputs.size() > 1) {
            System.out.println("unsupported number of return values");
            assert false;
        }

        VarDecl output = partEvalNode.outputs.get(0);
        for (Equation eq : partEvalNode.equations) {
            if (eq.lhs.toString().equals(output.id))
                return eq.expr;
        }
        return null;
    }

    private Expr findEqRhs(Expr expr) {
        if (!(expr instanceof IdExpr)) {
            System.out.println("unsupported collapsing of type. Aborting.");
            assert false;
        }

        for (Equation eq : repairNodeEqs) {
            if (eq.lhs.toString().equals(((IdExpr) expr).id))
                return eq.expr;
        }
        return null;
    }
}
