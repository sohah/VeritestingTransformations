package gov.nasa.jpf.symbc.veritesting.ast.visitors;

public class ForallAstVisitor extends AstIterVisitor<Boolean> {

    public ForallAstVisitor(ForallExprVisitor v) {
        super(v, (x, y) -> (x && y), Boolean.TRUE);
    }

}
