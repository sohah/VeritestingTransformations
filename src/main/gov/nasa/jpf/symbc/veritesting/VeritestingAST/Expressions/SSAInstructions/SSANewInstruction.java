
package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.classLoader.NewSiteReference;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * An allocation instruction ("new") for SSA form.
 * <p>
 * This includes allocations of both scalars and arrays.
 */
public class SSANewInstruction implements VeriExpression {
    private final int iindex;
    private final Var result;

    private final NewSiteReference site;

    /**
     * The value numbers of the arguments passed to the call. If params == null, this should be a static this statement allocates a
     * scalar. if params != null, then params[i] is the size of the ith dimension of the array.
     */
    private final VeriExpression[] params;

    /**
     * Create a new instruction to allocate a scalar.
     */
    protected SSANewInstruction(int iindex, Var result, NewSiteReference site) throws IllegalArgumentException {
        this.iindex = iindex;
        this.result = result;
        this.site = site;
        this.params = null;
    }

    protected SSANewInstruction(int iindex, Var result, NewSiteReference site, VeriExpression[] params) {
        this.iindex = iindex;
        if (params == null) {
            throw new IllegalArgumentException("params is null");
        }
        if (site == null) {
            throw new IllegalArgumentException("site is null");
        }
        this.result = result;
        this.site = site;
        this.params = new VeriExpression[params.length];
        System.arraycopy(params, 0, this.params, 0, params.length);
    }

    private String array2String(VeriExpression[] params) {
        StringBuffer result = new StringBuffer();
        for (int i = 0; i < params.length; i++) {
            result.append(params[i]);
            result.append(" ");
        }
        return result.toString();
    }

    public Var getResult() {
        return result;
    }

    public VeriExpression[] getParams() {
        return params;
    }

    public TypeReference getConcreteType() {
        return site.getDeclaredType();
    }

    public NewSiteReference getNewSite() {
        return site;
    }

    public int getIindex() {
        return iindex;
    }

    public VeriExpression getParamElement(int j) {
        return params[j];
    }


    public boolean isPEI() {
        return true;
    }

    @Override
    public String toString() {
        return result + " = new " + site.getDeclaredType() + "@" + site.getProgramCounter()
                + (params == null ? "" : array2String(params));
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitNewInstruction(this);
    }

}
