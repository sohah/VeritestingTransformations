package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.Collection;

public class Input extends SpecInputOutput {


    /**
     * converts bool to int form for SPF, it does not pre append initial value since this is really the input, we need to maintain the initial value for the output really of the first step.
     *
     * @return
     */
    public Pair<ArrayList<VarDecl>, ArrayList<Equation>> convertInput() { //convertBoolToSpfInt
        ArrayList<Equation> conversionEqList = new ArrayList<>();
        ArrayList<VarDecl> conversionLocalList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            String var = varList.get(i).getFirst();
            NamedType type = varList.get(i).getSecond();
            if (type == NamedType.BOOL) { //type conversion needed
                conversionLocalList.add(new VarDecl(var, NamedType.INT));
                String newVar = var + "_bool";
                varList.set(i, new Pair(newVar, NamedType.BOOL));
                IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new IdExpr(newVar), new IntExpr(1), new IntExpr(0));
                Equation conversionEq = new Equation(new IdExpr(var), ifThenElseExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return new Pair(conversionLocalList, conversionEqList);
    }

}
