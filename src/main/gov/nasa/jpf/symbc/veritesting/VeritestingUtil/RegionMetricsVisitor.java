package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.veritesting.ast.def.IfThenElseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;

public class RegionMetricsVisitor  extends AstMapVisitor {
    private int depth = 0;
    private int maxDepth = 0;
    private long totalNumPaths = 1;
    private long thisNumPaths = 1;

    private RegionMetricsVisitor() {
        super(new ExprMapVisitor());
    }

    @Override
    public Stmt visit(IfThenElseStmt a) {
        thisNumPaths++;
        depth++;
        if (depth > maxDepth) maxDepth = depth;
        a.thenStmt.accept(this);
        a.elseStmt.accept(this);
        depth--;
        if (depth == 0) {
            totalNumPaths *= thisNumPaths;
            thisNumPaths = 1;
        }
        return a;
    }


    public static boolean execute(StaticRegion staticRegion) {
        RegionMetricsVisitor visitor = new RegionMetricsVisitor();
        staticRegion.staticStmt.accept(visitor);
        staticRegion.maxDepth = visitor.maxDepth;
        staticRegion.totalNumPaths = visitor.totalNumPaths;
        return true;
    }
}
