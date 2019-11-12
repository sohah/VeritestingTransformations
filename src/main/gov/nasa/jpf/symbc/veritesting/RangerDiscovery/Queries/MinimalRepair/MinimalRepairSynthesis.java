package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeStatus;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ARepairSynthesis;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.TestCaseManager;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ThereExistsQuery;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.H_discovery;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.TNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.renameMainNode;


/**
 * This is used to synthize a tighter different repair, using the other part of the query for the forall, we ensure
 * that the repair is actually included in the old repair and is matching the specification.
 */
public class MinimalRepairSynthesis extends ThereExistsQuery {
    private Node lastKnownRepair;

    //these are the tighter holes that we are trying to find, these are different from "holes" which just hold the
    // to be repaired expressions.

    List<Hole> tighterHolesInput = new ArrayList<>();
    List<Hole> tighterHolesOutput = new ArrayList<>();

    /**
     * initial minimal repair is made from the last known good repair, not test cases yet, just new free variables as
     * well as a fixed node for last known repair.
     * @param aRepairSynthesis
     * @param lastRepairNode
     */
    public MinimalRepairSynthesis(ARepairSynthesis aRepairSynthesis, Node lastRepairNode) {
        //this is the initial synthesized program that we need to update with the new I', O' call.

        this.lastKnownRepair = lastRepairNode;
        List<Node> newNodes = createFixedNodePart(aRepairSynthesis.getSynthesizedProgram());
        newNodes.add(lastRepairNode); //this adds the constant R that we have found previously



        synthesizedProgram = aRepairSynthesis.getSynthesizedProgram();
        Pair<List<Hole>, List<Hole>>  tighterHolePair = makeNewTighterHoles(contract);
        tighterHolesInput = tighterHolePair.getFirst();
        tighterHolesOutput = tighterHolePair.getSecond();

        synNodeKey = aRepairSynthesis.getSynNodeKey();

        Node newMain = updateMain(synthesisSpecNode, tighterHolePair);

        List<Node> newNodes = new ArrayList<>();



        synthesizedProgram = new Program(synthesizedProgram.location, synthesizedProgram.types, synthesizedProgram
                .constants, synthesizedProgram
                .functions, newNodes, null, "main");
    }

    @Override
    protected List<Node> createFixedNodePart(Program holeProgram) {
        return holeProgram.nodes;
    }


    @Override
    protected Pair<List<VarDecl>, List<Equation>> createCheckSpeckLocals(Node synthesisSpecNode) {
        return null;
    }

    @Override
    protected Node createVariableNodePart(JKindResult counterExResult) {
        return null;
    }

    @Override
    protected List<VarDecl> createCheckSpecInput(List<VarDecl> synthesisInputs) {
        return null;
    }

    @Override
    protected Node createSynthesisMain(Node synthesisSpecNode) {
        return null;
    }

/*

    protected Node createVariableNodePart(JKindResult counterExResult) {
        testCaseManager = new TestCaseManager(contract, holes, counterExResult);
        Node holeMainNode = createSynthesisMain(synthesisSpecNode);
        return holeMainNode;
    }


    protected List<VarDecl> createCheckSpecInput(List<VarDecl> synthesisInputs) {
        List<VarDecl> inputs = new ArrayList<>();
        inputs.addAll(synthesisInputs);
        inputs.add(new VarDecl("k", NamedType.INT));
        return inputs;
    }

    protected Pair<List<VarDecl>, List<Equation>> createCheckSpeckLocals(Node synthesisSpecNode) {
        List<VarDecl> locals = new ArrayList<>();
        List<Equation> equations = new ArrayList<>();
        VarDecl stepVarDecl = new VarDecl("step", NamedType.INT);
        VarDecl stepOkVarDecl = new VarDecl("stepOK", NamedType.BOOL);

        locals.add(stepVarDecl);
        locals.add(stepOkVarDecl);

        IdExpr stepVarExpr = DiscoveryUtil.varDeclToIdExpr(stepVarDecl);
        IdExpr stepOkVarExpr = DiscoveryUtil.varDeclToIdExpr(stepOkVarDecl);

        IdExpr kExpr = new IdExpr("k");

        BinaryExpr stepIncRhs = new BinaryExpr(new IntExpr(0), BinaryOp.ARROW, new BinaryExpr(new IntExpr(1), BinaryOp.PLUS, new UnaryExpr(UnaryOp.PRE, stepVarExpr)));
        Equation stepIncrement = new Equation(stepVarExpr, stepIncRhs);

        equations.add(stepIncrement);

        BinaryExpr stepOkCond = new BinaryExpr(stepVarExpr, BinaryOp.LESSEQUAL, kExpr);

        NodeCallExpr thenStmt = new NodeCallExpr(TNODE, (ArrayList<Expr>) (ArrayList<?>) DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.inputs));

        IfThenElseExpr stepOkRhs = new IfThenElseExpr(stepOkCond, thenStmt, new BoolExpr(true));

        Equation stepOkEq = new Equation(stepOkVarExpr, stepOkRhs);
        equations.add(stepOkEq);

        BinaryExpr globalOkRhs1 = new BinaryExpr(stepVarExpr, BinaryOp.GREATEREQUAL, kExpr);

        assert (synthesisSpecNode.outputs.size() == 1);

        IdExpr globalOkLhs = DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.outputs.get(0));

        List<Expr> globalOkParameters = new ArrayList<>();
        globalOkParameters.add(stepOkVarExpr);
        NodeCallExpr globalOkRhs2 = new NodeCallExpr(H_discovery, globalOkParameters);
        Equation globalOkEq = new Equation(globalOkLhs, new BinaryExpr(globalOkRhs1, BinaryOp.AND, globalOkRhs2));
        equations.add(globalOkEq);

        return new Pair(locals, equations);
    }

    protected Node createSynthesisMain(Node synthesisSpecNode) {
        List<Expr> myAssertions = freezeHolesAssertion();

        List<VarDecl> myInputs = extractHoleEnteries(synthesisSpecNode.inputs);
        List<Equation> myEquations = new ArrayList<>();
        myEquations.addAll(testCaseManager.testInputEqs);
        myEquations.addAll(testCaseManager.testCallEqs);
        myEquations.add(testCaseManager.propertyEq);

        List<VarDecl> myLocals = new ArrayList<>();
        myLocals.addAll(new ArrayList<>());
        myLocals.addAll(testCaseManager.testInputVars);
        myLocals.addAll(testCaseManager.testCallVars);

        List<VarDecl> myOutput = new ArrayList<>();
        myOutput.add(new VarDecl("fail", NamedType.BOOL));

        List<String> myProperties = new ArrayList<>();
        myProperties.add("fail");


        return new Node("main", myInputs, myOutput, myLocals, myEquations, myProperties, myAssertions, synthesisSpecNode
                .realizabilityInputs, synthesisSpecNode.contract, synthesisSpecNode.ivc);
    }
*/


}
