package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import jkind.lustre.Expr;

import java.util.PriorityQueue;

public interface ExprHoleBuilder {
    PriorityQueue<CandidateRepairExpr> candidateQueue = new PriorityQueue<>(10);



    int computeCost();

    CandidateRepairExpr build();


}
