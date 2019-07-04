package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import java.util.PriorityQueue;

public interface ExprHoleBuilder {
    PriorityQueue<CandidateRepairExpr> candidateQueue = new PriorityQueue<>(10);

    public void createBuilder();

    public void build();

}
