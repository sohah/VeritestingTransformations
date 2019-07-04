package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;

import java.util.PriorityQueue;

public class CandidateSelectionMgr {
    PriorityQueue<CandidateRepairExpr> theQueue = new PriorityQueue<>(30);

    public CandidateSelectionMgr(){
        populateTheQueue();
    }

    private void populateTheQueue(){
        ConstantHoleBuilder constantHoleBuilder = new ConstantHoleBuilder();
    }

    public CandidateRepairExpr poll(){
        return theQueue.poll();
    }

    public int queueSize(){
        return theQueue.size();
    }

}
