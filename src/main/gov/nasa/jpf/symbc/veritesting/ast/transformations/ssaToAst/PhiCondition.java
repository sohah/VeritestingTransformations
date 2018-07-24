package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.ISSABasicBlock;
import za.ac.sun.cs.green.expr.Expression;

public class PhiCondition {
    public enum Branch {Then, Else};

    public final Branch branch;
    public final Expression condition;

    public PhiCondition(Branch branch, Expression condition) {
        this.branch = branch;
        this.condition = condition;
    }


}
