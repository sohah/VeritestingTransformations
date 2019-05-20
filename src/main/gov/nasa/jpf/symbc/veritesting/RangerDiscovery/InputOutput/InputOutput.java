package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;

public class InputOutput {
    public ArrayList<Pair<String, NamedType>> varList = new ArrayList<>();

    public void add(String start_btn, NamedType type) {
        varList.add(new Pair<>(start_btn, type));
    }

    public boolean contains(String varName, NamedType type) {
        for (int i = 0; i < varList.size(); i++) {
            if (varList.get(i).getFirst().equals(varName) && varList.get(i).getSecond().equals(type))
                return true;
        }
        return false;
    }

    public ArrayList<VarDecl> generateVarDecl() {
        ArrayList<VarDecl> varDeclList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            Pair<String, NamedType> var = varList.get(i);
            varDeclList.add(new VarDecl(var.getFirst(), var.getSecond()));
        }
        return varDeclList;
    }


    public ArrayList<Equation> convertInput() { //convertBoolToSpfInt
        ArrayList<Equation> conversionEqList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            String var = varList.get(i).getFirst();
            NamedType type = varList.get(i).getSecond();
            if (type == NamedType.BOOL) { //type conversion needed
                String newVar = var + "_bool";
                varList.set(i, new Pair(var, NamedType.BOOL));
                IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new IdExpr(newVar), new IntExpr(1), new IntExpr(0));
                Equation conversionEq = new Equation(new IdExpr(newVar), ifThenElseExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return conversionEqList;
    }

    public ArrayList<Equation> convertOutput() { // convertSpfIntToBool
        ArrayList<Equation> conversionEqList = new ArrayList<>();

        for (int i = 0; i < varList.size(); i++) {
            String var = varList.get(i).getFirst();
            NamedType type = varList.get(i).getSecond();
            if (type == NamedType.BOOL) { //type conversion needed
                String newVar = var + "_bool";
                varList.set(i, new Pair(newVar, NamedType.BOOL));
                IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new BinaryExpr(new IdExpr(var),BinaryOp.EQUAL, new
                        IntExpr
                        (1)), new BoolExpr(true), new BoolExpr(false));
                Equation conversionEq = new Equation(new IdExpr(newVar), ifThenElseExpr);
                conversionEqList.add(conversionEq);
            }

        }
        return conversionEqList;
    }
}
