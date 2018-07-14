package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

//SH: This class is a placeholder for a var that hasn't been created by WALA and might be
// replace later with VeritestingVar

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
