package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Statements;

import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;

public class Assignment implements VeriStatment {
    public Assignment(Var lhs, VeriExpression rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    private Var lhs;
    private VeriExpression rhs;

    public Var getLhs() {
        return lhs;
    }

    public VeriExpression getRhs() {
        return rhs;
    }

    @Override
    public String toString() {
        return lhs.toString() + " := (" + rhs.toString() +" )";
    }

    @Override
    public Object visit(VeriStatVisitor v) {
        return v.visitAssignment(this);
    }
}
