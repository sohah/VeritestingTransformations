package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;

import java.util.HashMap;
import java.util.List;

/**
 * contains the definition of some term for which the user/tool wants to repair with respect to some implementation.
 */
public class FaultyEquation {
    Program pgm;
    Node node;
    Equation eq;
    Expr def;
    Type defType;
    Expr rhs;
    HashMap<IdExpr, Type> useTypeMap = new HashMap<>();
    int maximumCost;

    public FaultyEquation(Program pgm, Equation eq, Node node) {
        if (eq.lhs.size() != 1) {
            System.out.println("Faulty equation needs to have a single def. Aborting!");
            assert false;
        }
        this.pgm = pgm;
        this.node = node;
        this.eq = eq;
        this.def = eq.lhs.get(0);
        this.defType = DiscoveryUtil.findExprType(def, node, pgm);
        this.rhs = eq.expr;
        fillUseTypeMap(); // has the side effect of populating the useTypeMap
        maximumCost = MaxCostFunction.compute(rhs);
    }

    private void fillUseTypeMap() {
        List<IdExpr> useList = discoverUse(rhs);
        for (int i = 0; i < useList.size(); i++) {
            IdExpr useExpr = useList.get(i);
            this.useTypeMap.put(useExpr, DiscoveryUtil.findExprType(useExpr, node, pgm));
        }
    }

    public HashMap<IdExpr, Type> getUseTypeMap() {
        return useTypeMap;
    }

    private List<IdExpr> discoverUse(Expr rhs) {
        return UseVisitor.execute(rhs);
    }
}
