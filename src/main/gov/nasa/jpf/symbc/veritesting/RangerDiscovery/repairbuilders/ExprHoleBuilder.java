package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repairbuilders;


import java.util.PriorityQueue;

public interface ExprHoleBuilder {
    PriorityQueue<CandidateRepairExpr> candidateQueue = new PriorityQueue<>(10);

    public void buildHoleCandidates();

    public void translateRepair();

}
