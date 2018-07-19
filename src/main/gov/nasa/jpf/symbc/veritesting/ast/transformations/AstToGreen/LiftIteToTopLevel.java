package gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen;

import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;

/**
 * Stub class; if we want to invert ifThenElse expressions, I will write it here.
 *
 * However, it is likely that this will be unnecessary if we can get Willem to
 * support ifThenElse expressions in Green.
 *
 */

public class LiftIteToTopLevel extends ExprMapVisitor {

    public LiftIteToTopLevel() {}

/*    public Expression visit(Operation expr) {
        Expression [] operands = new Expression [expr.getArity()];
        int index = 0;
        for (Expression e: expr.getOperands()) {
            operands[index++] = eva.accept(e);
        }
    }
*/
}
