package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;


import jkind.lustre.NamedType;

/**
 * This class is very important, it is establishes the names of the vars we need to collect their values in the counter example.
 * Because we have two cases of counter examples we might need to collect different things depending on which query are we doing and on which violation (isMatchingImpl or isTighter) did we encounter.
 * In all cases we collect the names identified here depending on the Purpose flag.
 *
 * This contains information about one of the inputs to the test cases, basically its name, where we can find it (if it is in main or in the wrapper. Note that we usually find in the wrapper the outputs of not matching implementation test cases while we look in the main for both the inputs as well as the outputs for untight testcases).
 * This class also contains information about the type of the var.
 * Finally this class pairs with every var if it is an input or if it is an output of the implementation, that means for test cases that results from not matching the implementation this is the output we need to collect.
 * Likewise the var can be the name of the output of the main this one captures the outputs that needs to be used for tightening.
 */


enum Purpose{INPUT, IMPLEMENTATIONOUTPUT, TIGHTEROUTPUT}

public class MainTCVar {
    String name;
    String location;
    NamedType type;
    Purpose purpose;


    public MainTCVar(String name, String inputLocation, NamedType type, Purpose purpose){
        this.name = name;
        location = inputLocation;
        this.type = type;
        this.purpose = purpose;
    }
}
