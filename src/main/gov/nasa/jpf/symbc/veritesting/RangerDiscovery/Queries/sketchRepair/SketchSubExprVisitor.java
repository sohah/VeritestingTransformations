package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import jkind.lustre.Expr;

import java.util.HashMap;

public class SketchSubExprVisitor extends ExprMapVisitor{
    public SketchSubExprVisitor(HashMap<Expr, Expr> paramToActualBindMap) {
        super();
    }
}
