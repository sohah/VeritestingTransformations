package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;

import java.util.*;

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

    private LinkedHashMap<IdExpr, Type> useTypeMap = new LinkedHashMap<>();
    List<IdExpr> nonUniqueUseList = new ArrayList<>();

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
        nonUniqueUseList = discoverUse(rhs);
        for (int i = 0; i < nonUniqueUseList.size(); i++) {
            IdExpr useExpr = nonUniqueUseList.get(i);
            if (isInUseMap(useExpr) == -1) //filtering already entered keys.
                this.useTypeMap.put(useExpr, DiscoveryUtil.findExprType(useExpr, node, pgm));
        }
    }

    private List<IdExpr> discoverUse(Expr rhs) {
        UseVisitor useVisitor = new UseVisitor();
        rhs.accept(useVisitor);
        return useVisitor.getUseList();
    }

    // since IdExpr does not define equals or hashcode, we can't keep them in the map and relay on the default way of java of fetching them. That is why this datastructure should not be accessable but operation on it can be accessable.
    public int isInUseMap(IdExpr idExpr) {
        int i = 0;
        for (Map.Entry e : useTypeMap.entrySet()) {
            if (e.getKey().toString().equals(idExpr.toString()))
                return i;
            ++i;
        }
        return -1; // indicating not found.
    }

    public int getNonUniqueUseListSize(){
        return nonUniqueUseList.size();
    }

}
