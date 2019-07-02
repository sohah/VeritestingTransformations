package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repairbuilders;

import jkind.lustre.Ast;
import jkind.lustre.Expr;

/**
 * computes the cost of an expression relative to another expression or a the maximum cost possible.
 */
public interface CostFunction {

    /**
     * computes the maximum cost of some expr, this will be the cost if all its leave expressions has changed and
     * will also count towards the cost of removing the expression.
     */
    static int computeMaximumCost(Expr expr) {

    }
}
