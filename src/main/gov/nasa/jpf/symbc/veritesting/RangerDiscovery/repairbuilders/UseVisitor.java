package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repairbuilders;

import jkind.lustre.*;
import jkind.lustre.visitors.ExprMapVisitor;

import java.util.ArrayList;
import java.util.List;

public class UseVisitor extends ExprMapVisitor {
    List<IdExpr> useList = new ArrayList<>();

    public static List<IdExpr> execute(Expr expr) {
        UseVisitor useVisitor = new UseVisitor();
        expr.accept(useVisitor);
        return useVisitor.useList;
    }

    @Override
    public Expr visit(IdExpr e) {
        if (!useList.contains(e))
            useList.add(e);
        return e;
    }

}
