package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.vm.Instruction;

public class RegionHitExactHeuristic{
    String regionKey;
    Instruction targetInstruction;
    boolean active;
    int pathCount = 0;

    public RegionHitExactHeuristic(String regionKey, Instruction targetInstruction, int pathCount) {
        this.regionKey = regionKey;
        this.targetInstruction = targetInstruction;
        this.pathCount = pathCount;
        active = true;
    }

    public boolean getRegionStatus() {
        return active;
    }

    public String getRegionKey() {
        return regionKey;
    }

    public Instruction getTargetInstruction() {
        return targetInstruction;
    }

    public void incrementPathCount() {
        ++pathCount;
    }

    public boolean equal(RegionHitExactHeuristic regionHitExactHeuristic) {
        if (this.regionKey.equals(regionHitExactHeuristic.regionKey))
            return true;
        else
            return false;
    }

    public String toString(){
        return regionKey + "\t\t\t\t" + targetInstruction + "\t\t\t\t" + active + "\t\t\t\t\t" + pathCount;
    }

    public String print(){
        return "regionKey = " + regionKey + ", targetInstruction = " + targetInstruction + ", active = " + active + ", pathcount = " + pathCount;
    }

    public void setActiveState(boolean state) {
        active = state;
    }
}


