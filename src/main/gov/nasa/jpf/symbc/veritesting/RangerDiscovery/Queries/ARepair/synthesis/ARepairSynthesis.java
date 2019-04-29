package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ThereExistsQuery;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeStatus;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.lustre.*;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.H_discovery;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.TNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.renameNode;


/**
 * This takes in the original program and build holes in the nodes we want to repair.
 * When repeatedly called, only the variable part is changed to contain the new test cases.
 * It implements the first query for the ThereExists that tries to find ARepair
 */
public class ARepairSynthesis extends ThereExistsQuery {


    public ARepairSynthesis(Contract contract, Program holeProgram, ArrayList<Hole> holes, JKindResult counterExResult, NodeRepairKey originalNodeKey) {
        ThereExistsQuery.contract = contract;

        ThereExistsQuery.holes = holes;

        //allnodes except main
        List<Node> nodes = createFixedNodePart(holeProgram);
        synNodeKey = originalNodeKey;

        synNodeKey.setNodesKey("main", NodeStatus.ARTIFICIAL);
        synNodeKey.setNodesKey(TNODE, NodeStatus.REPAIR);

        Node newMain = createVariableNodePart(counterExResult); //this creates the new main with the right test cases.

        nodes.add(newMain);
        synthesizedProgram = new Program(holeProgram.location, holeProgram.types, holeProgram.constants, holeProgram
                .functions, nodes, null, "main");
    }


    protected List<Node> createFixedNodePart(Program holeProgram) {
        List<Node> nodes = new ArrayList<>();

        nodes.addAll(holeProgram.nodes);
        nodes.add(getGloballyNode());

        Node mainNode = holeProgram.getMainNode();
        synthesisSpecNode = renameNode(TNODE, mainNode);

        nodes.set(nodes.indexOf(mainNode), synthesisSpecNode);

        nodes.add(createCheckSpecNode(synthesisSpecNode));
        return nodes;
    }


    /**
     * freezing all holes for this query.
     * @return
     */
    private List<Expr> freezeHolesAssertion() {
        List<Expr> freezeAssertions = new ArrayList<>();
        for (int i = 0; i < holes.size(); i++)
            freezeAssertions.add(makeFreezeSingleAssertion(holes.get(i).toString()));

        return freezeAssertions;
    }

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
        myOutput.add(new VarDecl(FAIL, NamedType.BOOL));

        List<String> myProperties = new ArrayList<>();
        myProperties.add(FAIL);


        return new Node("main", myInputs, myOutput, myLocals, myEquations, myProperties, myAssertions, synthesisSpecNode
                .realizabilityInputs, synthesisSpecNode.contract, synthesisSpecNode.ivc);
    }

    public void collectCounterExample(JKindResult counterExResult) {
        testCaseManager.collectCounterExample(counterExResult);
        synthesizedProgram = makeNewProgram(false);
    }

}
