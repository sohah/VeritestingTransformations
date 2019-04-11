package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.vm.Instruction;

public class RegionHitExactHeuristic {
    String regionKey;
    Instruction targetInstruction;
    boolean active ;
    int pathCount = 0;

    public RegionHitExactHeuristic(String regionKey, Instruction targetInstruction, int pathCount){
        this.regionKey = regionKey;
        this.targetInstruction = targetInstruction;
        this.pathCount = pathCount;
        active = true;
    }

}
