package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.Collection;

public class Output extends SpecInputOutput {



    public ArrayList<Equation> convertOutput() { // convertSpfIntToBool
        ArrayList<Equation> conversionEqList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            String var = varList.get(i).getFirst();
            NamedType type = varList.get(i).getSecond();
            if (type == NamedType.BOOL) { //type conversion needed
                String newVar = var + "_bool";
                varList.set(i, new Pair(newVar, NamedType.BOOL));
                IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new BinaryExpr(new IdExpr(var), BinaryOp.EQUAL, new
                        IntExpr
                        (1)), new BoolExpr(true), new BoolExpr(false));

                // this needs to be done in a seperate method that would get the initial value
                /*BinaryExpr initExpr = new BinaryExpr(new BoolExpr(false), BinaryOp.ARROW, ifThenElseExpr);
                Equation conversionEq = new Equation(new IdExpr(newVar), initExpr);*/

                Equation conversionEq = new Equation(new IdExpr(newVar), ifThenElseExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return conversionEqList;
    }


    /**
     * adds an initial value for a method output that needed not have an initial value.
     * @return
     */
    public Equation makeInitEq() {
        Expr initialValue = varInitValue.get(0).getSecond();
        return new Equation(new IdExpr(Config.methodReturnName), new BinaryExpr(initialValue, BinaryOp.ARROW, new IdExpr(varInitValueList.get(0).getFirst())));
    }
}
