package gov.nasa.jpf.symbc.veritesting.Heuristics;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.RegionHitExactHeuristic;

import java.util.ArrayList;


public class HeuristicManager {


    /**
     * used to collect all regions that we hit along with the number of paths that SPF had to explore through it.
     * An invariant here is that the last added element is the element that we wish to count its paths, if we are still
     * in the heuristic choices.
     */
    private static ArrayList<RegionHitExactHeuristic> regionHitExactHeuristicArray = new ArrayList<>();


    public static void addRegionExactHeuristic(RegionHitExactHeuristic regionHitExactHeuristic) {
        if (!regionHitExactHeuristicArray.contains(regionHitExactHeuristic))
            regionHitExactHeuristicArray.add(regionHitExactHeuristic);
    }

    public static PathStatus incrementRegionExactHeuristicCount(gov.nasa.jpf.vm.Instruction instructionToExecute) {
        RegionHitExactHeuristic regionHeuristic = HeuristicManager.getRegionHeuristic();
        if (regionHeuristic.getRegionStatus()){
            if (instructionToExecute.toString().equals(regionHeuristic.getTargetInstruction().toString())) {
                regionHeuristic.incrementPathCount();
                return PathStatus.ENDREACHED; //returns true if we are trying to count paths, whether we hit end instruction or not.
            }
            return PathStatus.INHEURISTIC;
        }
        return PathStatus.OUTHEURISTIC;
    }

    public static void regionHeuristicFinished(String key) {
        RegionHitExactHeuristic regionHeuristic = regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
        if (!key.equals(regionHeuristic.getRegionKey())) {
            System.out.println("unexpected region for heuristics.");
            assert false;
        }

        if (!regionHeuristic.getRegionStatus()) {
            System.out.println("expecting region heuristic in 'active status'!");
            assert false;
        }
        regionHeuristic.setActiveState(false);
    }

    public static boolean getRegionHeuristicStatus(String key) {
        RegionHitExactHeuristic regionHeuristic = regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
        if (!key.equals(regionHeuristic.getRegionKey())) {
            System.out.println("unexpected region for heuristics.");
            assert false;
        }
        return regionHeuristic.getRegionStatus();
    }

    public static RegionHitExactHeuristic getRegionHeuristic() {
        assert (regionHitExactHeuristicArray.size() != 0);
        return regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
    }

    public static void printStatistics() {
        System.out.println("RegionKey\t\t\t\t\t\tTargetInstruction\t\t\t\tActiveStatus\t\t\tPathCount");
        for (RegionHitExactHeuristic regionHeuristic : regionHitExactHeuristicArray) {
            System.out.println(regionHeuristic.toString());
        }
    }

    public static int getRegionHeuristicSize() {
        return regionHitExactHeuristicArray.size();
    }
}
