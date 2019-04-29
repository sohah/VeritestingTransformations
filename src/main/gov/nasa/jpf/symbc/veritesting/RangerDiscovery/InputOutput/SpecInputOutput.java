package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

public class SpecInputOutput {
    public ArrayList<Pair<String, NamedType>> varList = new ArrayList<>();


    int size = 0;

    public void add(String start_btn, NamedType type) {
        varList.add(new Pair<>(start_btn, type));
        size++;

    }

    public boolean contains(String varName, NamedType type) {
        for (int i = 0; i < varList.size(); i++) {
            if (varList.get(i).getFirst().equals(varName) && varList.get(i).getSecond().equals(type))
                return true;
        }
        return false;
    }

// checks if the name of the variable exists
    public boolean hasName(String varName) {
        for (int i = 0; i < varList.size(); i++) {
            if (varList.get(i).getFirst().equals(varName))
                return true;
        }
        return false;
    }

    public List<String> getInputNames(){
        List<String> names = new ArrayList<>();

        for(int i=0; i<varList.size(); i++){
            names.add(varList.get(i).getFirst());
        }

        return names;
    }

    public int getSize() {
        return size;
    }


    public boolean containsBool(){
        for(int i=0; i< varList.size(); i++)
            if (varList.get(i).getSecond() == NamedType.BOOL)
                return true;

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


    //this is very specific to r_wrapper and is used particularly to replicate the methodOutput, that is part of the state, to become the output of the wrapper.
    public Pair<VarDecl, Equation> replicateMe(String myNewName) {
        assert (varList.size() == 1);

        Pair<String, NamedType> methodOutVar = varList.get(0);

        VarDecl out = new VarDecl(myNewName, methodOutVar.getSecond());

        Equation outEq = new Equation(DiscoveryUtil.varDeclToIdExpr(out), new IdExpr(methodOutVar.getFirst()));

        return new Pair(out, outEq);
    }

}
