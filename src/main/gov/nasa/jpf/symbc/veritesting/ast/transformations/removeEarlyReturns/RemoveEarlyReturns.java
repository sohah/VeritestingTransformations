package gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns;

import gov.nasa.jpf.symbc.veritesting.ast.def.Stmt;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.AstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprIdVisitor;
import za.ac.sun.cs.green.expr.Expression;

import java.util.Deque;
import java.util.LinkedList;

/*
    We need to know the return type (it is not present in the SR itself)

    We need to add support for
 */

public class RemoveEarlyReturns extends AstMapVisitor {

    // Don't transform expressions
    private static final ExprIdVisitor exprVisitor = new ExprIdVisitor();
    private Deque<Expression> conditionList = new LinkedList<>();


    private RemoveEarlyReturns() {
        super(exprVisitor);
    }

    // After transformation, there will be a single return statement at the
    // end of the block that is conditionally assigned.
    // Throws an IllegalArgumentException exception if there is some case
    // where the set of return statements is not a complete set (so we don't
    // know what to assign the return value) - this should never happen.

    // So...each
    //

    public static Stmt removeEarlyReturns(Stmt stmt) {
        RemoveEarlyReturns rer = new RemoveEarlyReturns();

        return null;
    }
}
