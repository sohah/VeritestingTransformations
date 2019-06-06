package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.lustre.*;
import jkind.lustre.parsing.LustreParseUtil;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.renameMainNode;

public class SynthesisContract {

    private Program synthesisProgram;
    public final Contract contract;

    private static ArrayList<Hole> holes;

    private static TestCaseManager testCaseManager;
    private static Node synthesisSpecNode;


    public SynthesisContract(Contract contract, String fileName, JKindResult counterExResult) throws IOException {
        this.contract = contract;
        Program holeProgram = ConstHoleVisitor.executeMain(LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(fileName)), "UTF-8")));
        holes = new ArrayList<>(ConstHoleVisitor.getHoles());

        List<Node> nodes = createFixedNodePart(holeProgram);
        DiscoverContract.changeMainToTNODE();
        Node newMain = createVariableNodePart(counterExResult); //this creates the new main with the right test cases.

        nodes.add(newMain);
        synthesisProgram = new Program(holeProgram.location, holeProgram.types, holeProgram.constants, holeProgram.functions, nodes, "main");
    }

    private Node createVariableNodePart(JKindResult counterExResult) {
        testCaseManager = new TestCaseManager(contract, counterExResult);
        Node holeMainNode = createSynthesisMain(synthesisSpecNode);
        return holeMainNode;
    }

    private List<Node> createFixedNodePart(Program holeProgram) {
        List<Node> nodes = new ArrayList<>();

        nodes.addAll(holeProgram.nodes);
        nodes.add(getGloballyNode());

        Node mainNode = holeProgram.getMainNode();
        synthesisSpecNode = renameMainNode(DiscoverContract.TNODE, mainNode);

        nodes.set(nodes.indexOf(mainNode), synthesisSpecNode);

        nodes.add(createCheckSpecNode(synthesisSpecNode));
        return nodes;
    }

    public void collectCounterExample(JKindResult counterExResult) {
        testCaseManager.collectCounterExample(counterExResult);
        synthesisProgram = makeNewProgram();
    }

    public Program getSynthesisProgram() {
        return synthesisProgram;
    }

    public static List<Expr> getHoleExpr() {
        List<Expr> holeExprs = new ArrayList<>();
        for (int i = 0; i < ConstantHole.getCurrentHolePrefix(); i++) {
            holeExprs.add(new IdExpr(ConstantHole.recreateHoleName(i)));
        }
        return holeExprs;
    }

    private Node createCheckSpecNode(Node synthesisSpecNode) {
        String id = DiscoverContract.CHECKSPECNODE;
        List<VarDecl> inputs = createSynthesisInput(synthesisSpecNode.inputs);
        List<VarDecl> outputs = synthesisSpecNode.outputs;
        Pair<List<VarDecl>, List<Equation>> localsEqPair = createCheckSpeckLocals(synthesisSpecNode);
        List<VarDecl> locals = localsEqPair.getFirst();
        List<Equation> equations = localsEqPair.getSecond();
        List<String> properties = null;
        List<Expr> assertions = null;
        List<String> ivc = null;
        List<String> realizabilityInputs = null; // Nullable
        jkind.lustre.Contract contract = null; // Nullable

        return new Node(id, inputs, outputs, locals, equations, properties, assertions, realizabilityInputs, contract, ivc);

    }

    private List<VarDecl> createSynthesisInput(List<VarDecl> synthesisInputs) {
        List<VarDecl> inputs = new ArrayList<>();
        inputs.addAll(synthesisInputs);
        inputs.add(new VarDecl("k", NamedType.INT));
        return inputs;
    }

    private Pair<List<VarDecl>, List<Equation>> createCheckSpeckLocals(Node synthesisSpecNode) {
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

        NodeCallExpr thenStmt = new NodeCallExpr(DiscoverContract.TNODE, (ArrayList<Expr>) (ArrayList<?>) DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.inputs));

        IfThenElseExpr stepOkRhs = new IfThenElseExpr(stepOkCond, thenStmt, new BoolExpr(true));

        Equation stepOkEq = new Equation(stepOkVarExpr, stepOkRhs);
        equations.add(stepOkEq);

        BinaryExpr globalOkRhs1 = new BinaryExpr(stepVarExpr, BinaryOp.GREATER, kExpr);

        assert (synthesisSpecNode.outputs.size() == 1);

        IdExpr globalOkLhs = DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.outputs.get(0));

        List<Expr> globalOkParameters = new ArrayList<>();
        globalOkParameters.add(stepOkVarExpr);
        NodeCallExpr globalOkRhs2 = new NodeCallExpr("H", globalOkParameters);
        Equation globalOkEq = new Equation(globalOkLhs, new BinaryExpr(globalOkRhs1, BinaryOp.AND, globalOkRhs2));
        equations.add(globalOkEq);

        return new Pair(locals, equations);
    }

    private Node createSynthesisMain(Node synthesisSpecNode) {
        List<Expr> myAssertions = freezeHolesAssertion();


        List<Equation> myEquations = new ArrayList<>();
        myEquations.addAll(testCaseManager.testInputEqs);
        myEquations.addAll(testCaseManager.testCallEqs);
        myEquations.add(testCaseManager.propertyEq);

        List<VarDecl> myLocals = new ArrayList<>();
        myLocals.addAll(new ArrayList<>());
        myLocals.addAll(testCaseManager.testInputVars);
        myLocals.addAll(testCaseManager.testCallVars);

        List<String> myProperties = new ArrayList<>();
        myProperties.add("ok");


        return new Node("main", synthesisSpecNode.inputs, synthesisSpecNode.outputs, myLocals, myEquations, myProperties, myAssertions, synthesisSpecNode.realizabilityInputs, synthesisSpecNode.contract, synthesisSpecNode.ivc);
    }

    private List<Expr> freezeHolesAssertion() {
        List<Expr> freezeAssertions = new ArrayList<>();

        for (int i = 0; i < ConstantHole.getCurrentHolePrefix(); i++) {
            String holeName = ConstantHole.recreateHoleName(i);
            BinaryExpr currentEqPreExr = new BinaryExpr(new IdExpr(holeName), BinaryOp.EQUAL, new UnaryExpr(UnaryOp.PRE, new IdExpr(holeName)));
            BinaryExpr assertion = new BinaryExpr(new BoolExpr(true), BinaryOp.ARROW, currentEqPreExr);
            freezeAssertions.add(assertion);
        }
        return freezeAssertions;
    }


    @Override
    public String toString() {
        return synthesisProgram.toString();
    }

    public Node getGloballyNode() {
        VarDecl inVarDecl = new VarDecl("in", NamedType.BOOL);
        VarDecl outVarDecl = new VarDecl("out", NamedType.BOOL);

        IdExpr inVarExpr = DiscoveryUtil.varDeclToIdExpr(inVarDecl);
        IdExpr outVarExpr = DiscoveryUtil.varDeclToIdExpr(outVarDecl);


        String id = DiscoverContract.GLOBALYNODE;
        List<VarDecl> inputs = new ArrayList<>();
        inputs.add(inVarDecl);

        List<VarDecl> outputs = new ArrayList<>();
        outputs.add(outVarDecl);

        List<VarDecl> locals = new ArrayList<>();

        List<Equation> equations = new ArrayList<>();
        BinaryExpr rhs = new BinaryExpr(inVarExpr, BinaryOp.ARROW, new BinaryExpr(inVarExpr, BinaryOp.AND, new UnaryExpr(UnaryOp.PRE, outVarExpr)));

        Equation globallyEq = new Equation(outVarExpr, rhs);
        equations.add(globallyEq);

        List<String> properties = new ArrayList<>();
        List<Expr> assertions = new ArrayList<>();
        List<String> ivc = new ArrayList<>();
        List<String> realizabilityInputs = null; // Nullable
        jkind.lustre.Contract contract = null; // Nullable

        return new Node(id, inputs, outputs, locals, equations, properties, assertions, realizabilityInputs, contract, ivc);
    }


    /**
     * This creates a new program by changing the main to a new main that contains the test case being generated using the counterExampleManager
     */
    private Program makeNewProgram() {

        Node oldMain = synthesisProgram.getMainNode();
        Node newMain = changeMainNode(oldMain);

        ArrayList<Node> nodes = new ArrayList<>();
        nodes.addAll(synthesisProgram.nodes);
        int mainIndex = nodes.indexOf(oldMain);

        nodes.set(mainIndex, newMain);

        return new Program(Location.NULL, synthesisProgram.types, synthesisProgram.constants, synthesisProgram.functions, nodes, "main");
    }

    private Node changeMainNode(Node mainNode) {
        List<VarDecl> locals = new ArrayList<>();
        locals.addAll(testCaseManager.testCallVars);
        locals.addAll(testCaseManager.testInputVars);

        List<Equation> equations = new ArrayList<>();
        equations.addAll(testCaseManager.testInputEqs);
        equations.addAll(testCaseManager.testCallEqs);
        equations.add(testCaseManager.propertyEq);

        return new Node(mainNode.id, mainNode.inputs, mainNode.outputs, locals, equations, mainNode.properties, mainNode.assertions, mainNode.realizabilityInputs, mainNode.contract, mainNode.ivc);
    }

    public ArrayList<Hole> getHoles() {
        return holes;
    }
}
