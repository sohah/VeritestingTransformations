package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;

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
}
