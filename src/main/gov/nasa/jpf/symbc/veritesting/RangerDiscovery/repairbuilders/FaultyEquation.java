package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repairbuilders;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;

import java.util.HashMap;
import java.util.List;

/**
 * contains the definition of some term for which the user/tool wants to repair with respect to some implementation.
 */
public class FaultyEquation {
    Node node;
    Equation eq;
    Expr def;
    Type defType;
    Expr rhs;
    HashMap<IdExpr, Type> useTypeMap = new HashMap<>();
    int maximumCost;

    public FaultyEquation(Equation eq, Node node) {
        if (eq.lhs.size() == 1) {
            System.out.println("Faulty equation needs to have a single def. Aborting!");
            assert false;
        }
        this.node = node;
        this.eq = eq;
        this.def = eq.lhs.get(0);
        this.defType = DiscoveryUtil.findExprType(def, node);
        this.rhs = eq.expr;
        fillUseTypeMap(useTypeMap);
        maximumCost = CostFunction.computeMaximumCost(rhs);
    }

    private void fillUseTypeMap(HashMap<IdExpr, Type> useTypeMap) {
        List<IdExpr> useList = discoverUse(rhs);
        for (int i = 0; i < useList.size(); i++) {
            IdExpr useExpr = useList.get(i);
            this.useTypeMap.put(useExpr, DiscoveryUtil.findExprType(useExpr, node));
        }
    }

    private List<IdExpr> discoverUse(Expr rhs) {
        return UseVisitor.execute(rhs);
    }
}
