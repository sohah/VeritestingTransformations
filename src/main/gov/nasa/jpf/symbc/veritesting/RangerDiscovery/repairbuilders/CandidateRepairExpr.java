package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repairbuilders;

import jkind.lustre.Expr;

/**
 * The invariant here is that at least one Hole expression exists as a leaf somewhere in expr.
 */
public class CandidateRepairExpr implements Comparable<CandidateRepairExpr> {
    Expr expr;
    int cost;

    public CandidateRepairExpr(Expr expr, int cost) {
        this.expr = expr;
        this.cost = cost;
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
    public int hashCode(){
        return this.expr.toString().hashCode();
    }

    @Override
    public String toString() {
        return ("," + expr.toString() + "," + cost + ")");
    }
}
