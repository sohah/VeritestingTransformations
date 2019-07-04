package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;

import java.util.List;
import java.util.PriorityQueue;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.faultyEquation;

public class ConstantHoleBuilder implements ExprHoleBuilder {
    List<List<Character>> permutation;


    public ConstantHoleBuilder(){
        permutation = DiscoveryUtil.computePermutation(faultyEquation.getUseTypeMap().size());
    }
    @Override
    public void createBuilder() {


    }

    @Override
    public void build() {


    }
}
