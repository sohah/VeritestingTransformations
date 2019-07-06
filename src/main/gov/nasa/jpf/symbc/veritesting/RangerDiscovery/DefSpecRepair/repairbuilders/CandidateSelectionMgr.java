package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;

import java.util.PriorityQueue;

public class CandidateSelectionMgr {
    PriorityQueue<CandidateRepairExpr> theQueue = new PriorityQueue<>(30);

    public CandidateSelectionMgr(){
        populateTheQueue();
    }

    //we can have many builders, constant builders, idExpr builders, pre builders, linear combination builders.
    private void populateTheQueue(){
        theQueue.addAll(ConstantHoleBuilder.execute());
    }

    public CandidateRepairExpr poll(){
        return theQueue.poll();
    }

    public int queueSize(){
        return theQueue.size();
    }

}
