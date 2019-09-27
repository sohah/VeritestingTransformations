package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;

public class ContractOutput extends Output {

    public void addInit(String var, Expr expr) {
        varInitValuePair.add(new Pair<>(var, expr));
    }

    //This initial value was mainly added to support outputing the inital value as the first step, to align with the spec. If we moved towards unchecking the spec in the first step then this is no longer useful.
    public ArrayList<Pair<String, Expr>> varInitValuePair = new ArrayList<>();

    public Expr getReturnInitVal(String name) {
        for(Pair<String,Expr> varInitPair: varInitValuePair){
            if(varInitPair.getFirst().equals(name))
                return varInitPair.getSecond();
        }
        assert false; //this method must be called for method output vars for which we must have an initalization.
        return null;
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

*/
    /*public Equation addInitToEq(Equation eq) {
        Expr initialValue = varInitValuePair.getSecond();
        return DiscoveryUtil.addInitToEq(eq, initialValue);

    }*/
}
