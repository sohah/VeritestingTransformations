package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;

import jkind.lustre.*;
import jkind.lustre.visitors.ExprMapVisitor;

import java.util.ArrayList;
import java.util.List;

/**
 * The invariant here, even though it is not checked, that the expressions are visited and populated in the list in
 * left most-depth-first order.
 */
public class UseVisitor extends ExprMapVisitor {
    List<IdExpr> useList = new ArrayList<>();

    @Override
    public Expr visit(IdExpr e) { //adding the list of uses even if it is repeated.
        useList.add(e);
        return e;
    }

    public List<IdExpr> getUseList() {
        return useList;
    }
}
