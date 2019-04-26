package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.ArrayList;

public class InputOutput {
    public ArrayList<Pair<String,Type>> varList = new ArrayList<>();

    public void add(String start_btn, Type type) {
        varList.add(new Pair<>(start_btn, type));
    }
}
