package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DefSpecRepair.repairbuilders;


import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprMapVisitor;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;

import java.util.ArrayList;
import java.util.List;
import java.util.PriorityQueue;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.faultyEquation;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.IdExprToVarDecl;

public class ConstantHoleBuilder extends UseVisitor implements ExprHoleBuilder {
    List<List<Character>> permutation;
    List<Character> currentPermutation;

    //accumulates all the varDeclaratio ns for holes that are defined while visiting a specific node, though an instance of this class.
    private List<VarDecl> holeVarDecl = new ArrayList<>();


    public ConstantHoleBuilder() {
        permutation = DiscoveryUtil.computePermutation(faultyEquation.getNonUniqueUseListSize());
        build();
    }

    @Override
    public void computeCost() {


    }

    @Override
    public void build() {
        for (int i = 0; i < permutation.size(); i++) {//enqueue one expression for each permutation with the right cost
            currentPermutation = permutation.get(i);
        }

    }

    @Override
    public Expr visit(IdExpr e) {
        super.visit(e);
        if (currentPermutation.get(useList.get(useList.size() - 1)) == '1')
            return createAndPopulateHole(e, )
            else
        return e;
    }

    private Expr createAndPopulateHole(Expr e, NamedType type) {
        ConstantHole newHole = new ConstantHole("");
        holeToConstantMap.put(newHole, new Pair(e, null));
        VarDecl newVarDecl = IdExprToVarDecl(newHole, type);
        if (Config.loopCount == 0) //initial run, then setup the holes.
            DiscoverContract.holeRepairState.createNewHole(newHole, e, type);
        this.holeVarDecl.add(newVarDecl);
        return newHole;
    }
}
