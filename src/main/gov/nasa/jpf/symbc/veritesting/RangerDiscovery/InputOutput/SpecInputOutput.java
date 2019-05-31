package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

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
}
