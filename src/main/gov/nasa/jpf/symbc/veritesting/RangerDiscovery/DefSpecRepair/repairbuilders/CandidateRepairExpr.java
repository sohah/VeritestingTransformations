package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.Hole;
import jkind.lustre.Expr;
import jkind.lustre.VarDecl;
import jkind.results.Counterexample;

import java.util.Map;
import java.util.Set;

/**
 * The invariant here is that at least one Hole expression exists as a leaf somewhere in expr.
 */
public class CandidateRepairExpr implements Comparable<CandidateRepairExpr> {
    public final Expr expr;
    public final int cost;

    // this is unordered should not be used for order related holes, but could be used as a lookup for the varDecl of the hole. Since Hole is implementing hashCode this data structure contains non-repeated elements.
    Map<Hole, VarDecl> holeVarDeclLookup;

    /*// contains the set of holes inside the expression, ordering here is not important because it the holes is already created.
    Set<Hole> holeSet;
*/
    public CandidateRepairExpr(Expr expr, int cost, Map<Hole, VarDecl> holeVarDeclMap) {
        this.expr = expr;
        this.cost = cost;
        this.holeVarDeclLookup = holeVarDeclMap;
  //      this.holeSet = holeSet;
    }

    @Override
    public int compareTo(CandidateRepairExpr expr) {
        if (this.cost > expr.cost)
            return 1;
        else if (this.cost < expr.cost)
            return -1;

        return 0;
    }

    /**
     * equality of objects is based on the string representation of the two expressions, regardless of the cost.
     *
     * @param o
     * @return
     */
    @Override
    public boolean equals(Object o) {
        if ((o != null) && (o instanceof CandidateRepairExpr))
            return this.expr.toString().equals(((CandidateRepairExpr) o).expr.toString());
        else
            return false;
    }


    @Override
    public int hashCode() {
        return this.expr.toString().hashCode();
    }

    @Override
    public String toString() {
        return ("," + expr.toString() + "," + cost + ")");
    }

    public Expr repairWithValues(Counterexample counterexample) {
        //return repaired expression, either by visiting the expression or by substituting the right library node. for now it is unimplemented
        System.out.print("unimplemented!");
        return null;
    }

    public Map<Hole, VarDecl> getHoleMap() {
        return holeVarDeclLookup;
    }

    /*public Set<Hole> getHoleSet() {
        return holeSet;
    }*/
}
