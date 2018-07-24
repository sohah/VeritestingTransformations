package gov.nasa.jpf.symbc.veritesting.ast.visitors;


import java.util.function.BinaryOperator;

public class ForallExprVisitor extends ExprIterVisitor<Boolean> {
    public ForallExprVisitor() {
        super((x, y) -> (x && y), Boolean.TRUE);
    }

}
