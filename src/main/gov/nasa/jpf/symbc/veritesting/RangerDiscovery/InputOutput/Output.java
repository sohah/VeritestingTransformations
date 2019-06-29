package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;

public class Output extends SpecInputOutput {


    /**
     * This adds converts the int of spf to a bool type output for the spec, while doing that, it uses the initial value "false" to define the initial value for the first step.
     * This initial value can be entered and mainpulated by the method output but we as of now thinking to remove not enforce the property check and repair on the first step and thereby this definition and adjustement we should remove it.
     * @return
     */

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
                BinaryExpr initExpr = new BinaryExpr(new BoolExpr(false), BinaryOp.ARROW, ifThenElseExpr);

                Equation conversionEq = new Equation(new IdExpr(newVar), initExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return conversionEqList;
    }
}
