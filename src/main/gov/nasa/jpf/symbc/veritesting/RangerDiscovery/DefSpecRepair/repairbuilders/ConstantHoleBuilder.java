package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;
import jkind.lustre.values.Value;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.faultyEquation;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.IdExprToVarDecl;

/**
 * This class permutes all possible permutation of holes for constants and populates the queue depending on these values.
 * it extends UseVisitor to gaurantee the same traversal and use that to find the current permutation value for that index.
 */
public class ConstantHoleBuilder extends UseVisitor implements ExprHoleBuilder {


    private final List<Character> currentPermutation;

    //accumulates all the varDeclarations for holes that are defined while visiting a specific node, though an instance of this class.
    private Map<Hole, VarDecl> holeVarDecl = new HashMap<>();

    // accumulates all the holes and the old constant value that they are replacing.
    private static HashMap<Hole, Pair<Ast, Value>> holeToConstantMap = new HashMap<>();

    public ConstantHoleBuilder(List<Character> currentPermutation) {
        super();
        this.currentPermutation = currentPermutation;
    }

    @Override
    public Expr visit(IntExpr e) {
        super.visit(e);
        if (currentPermutation.get(contantUseList.size() - 1).equals("1"))
            return createAndPopulateHole(e, NamedType.INT);
        else
            return e;
    }

    @Override
    public Expr visit(BoolExpr e) {
        super.visit(e);
        if (currentPermutation.get(contantUseList.size() - 1).charValue() == '1')
            return createAndPopulateHole(e, NamedType.BOOL);
        else
            return e;
    }


    private Expr createAndPopulateHole(Expr e, NamedType type) {
        ConstantHole newHole = new ConstantHole("");
        holeToConstantMap.put(newHole, new Pair(e, null));
        VarDecl newVarDecl = IdExprToVarDecl(newHole, type);
        /*if (Config.loopCount == 0) //initial run, then setup the holes.
            DiscoverContract.holeRepairState.createNewHole(newHole, e, type);*/
        this.holeVarDecl.put(newHole, newVarDecl);
        return newHole;
    }

    @Override
    public int computeCost() { // cost is computed as every change of delete and insert.
        String currentPermutationStr = currentPermutation.stream().map(e -> e.toString()).reduce((acc, e) -> acc + e).get();
        int numberOfOnes = currentPermutationStr.length() - currentPermutationStr.replaceAll("1", "").length();
        return Integer.bitCount(numberOfOnes);
    }

    @Override
    public CandidateRepairExpr build() {
        Expr candidateRepairExpr = faultyEquation.rhs.accept(this);
        int cost = computeCost();
        return new CandidateRepairExpr(candidateRepairExpr, cost, holeVarDecl);
    }

    public static PriorityQueue<CandidateRepairExpr> execute() {
        List<List<Character>> permutation = DiscoveryUtil.computePermutation(faultyEquation.getContantUseListSize());

        //for loop needs to start from one because we want to ignore the permutation of all zeros.
        for (int i = 1; i < permutation.size(); i++) {//enqueue one expression for each permutation with the right cost
            ConstantHole.resetCount(); //resets the numbering of holes.
            List<Character> currentPermutation = permutation.get(i);
            ConstantHoleBuilder constantHoleBuilder = new ConstantHoleBuilder(currentPermutation);
            CandidateRepairExpr candidateExpr = constantHoleBuilder.build();
            candidateQueue.add(candidateExpr);
        }
        return candidateQueue;
    }
}
