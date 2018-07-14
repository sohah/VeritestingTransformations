package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions;

public class WalaVar implements Var{

    private int var;

    public WalaVar(int var) {
        this.var = var;
    }


    @Override
    public Var getVar() {
        return this;
    }

    @Override
    public void setVar(Var variable) {
        this.var = ((WalaVar)variable).var;
    }

    @Override
    public String toString() {
        return String.valueOf(var);
    }

    @Override
    public void visit(VeriExpressionVisitor v) {

    }
}
