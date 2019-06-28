package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;

// it is always the case that there is only a single element in the method output, i.e., it is a singleton.
public class MethodOutput extends Output {
    public boolean hasConversion;

    public void addInit(String var, Expr expr) {
        varInitValuePair = new Pair<>(var, expr);
    }

    //This initial value was mainly added to support outputing the inital value as the first step, to align with the spec. If we moved towards unchecking the spec in the first step then this is no longer useful.
    public Pair<String, Expr> varInitValuePair;

    public Expr getReturnInitVal() {
        return varInitValuePair.getSecond();
    }

    /**
     * adds an initial value for a method output that needed not have an initial value.
     *
     * @return
     */
    /*public Equation makeInitEq() {
        Expr initialValue = varInitValueList.get(0).getSecond();
        return new Equation(new IdExpr(Config.methodReturnName), new BinaryExpr(initialValue, BinaryOp.ARROW, new IdExpr(varInitValueList.get(0).getFirst())));
    }


    public Equation addInitToEq(Equation eq) {
        assert varInitValueList.size() ==1 && varList.size() ==1;
        Expr initialValue = varInitValueList.get(0).getSecond();

        return DiscoveryUtil.addInitToEq(eq, initialValue);

    }*/
}
