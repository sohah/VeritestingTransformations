package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class EmptyVar implements Var{
    @Override
    public Var getVar() {
        return null;
    }

    @Override
    public void setVar(Var var) {
    }

    @Override
    public void visit(VeriExpressionVisitor v) {

    }

    @Override
    public String toString() { return "EmptyVar";  }

}
