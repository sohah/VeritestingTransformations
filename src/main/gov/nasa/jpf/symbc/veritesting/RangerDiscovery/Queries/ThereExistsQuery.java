package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.TestCaseManager;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.CHECKSPECNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.H_discovery;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.findEqWithLhs;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.removeEqWithLhs;


/**
 * This is the abstract class of any ThereExists Query. The main components are T_node, checkspec node which we'll
 * construct, a bunch of holes, freezing constraints on the holes, test cases, and a main.
 */
public abstract class ThereExistsQuery {

    protected Program synthesizedProgram; //the outcome of this class is the creation of this finally
    // synthesized/repaired program

    //original contract mapping
    public static Contract contract;

    //these are all the nodes in the program
    protected static ArrayList<Hole> holes;

    //this is the test case manager that manages all test cases
    protected static TestCaseManager testCaseManager;

    //this is the T_node that we want to synthesize its inner expressions.
    protected static Node synthesisSpecNode;

    protected NodeRepairKey synNodeKey = new NodeRepairKey();

    //this creates the local variables for the checkspec node.
    protected abstract Pair<List<VarDecl>, List<Equation>> createCheckSpeckLocals(Node synthesisSpecNode);

    //this creates the fixed part of the syntheized program which contains the checkspec without any test cases just
    //yet.
    protected abstract List<Node> createFixedNodePart(Program holeProgram);

    //this creates the varaible part of the synthesized program, which is variable because of the additional test cases.
    protected abstract Node createVariableNodePart(JKindResult counterExResult);

    //this creates the input of the checkspec node.
    protected abstract List<VarDecl> createCheckSpecInput(List<VarDecl> synthesisInputs);


    //this creates the new main node for the syntheized program.
    protected abstract Node createSynthesisMain(Node synthesisSpecNode);


    public final static String FAIL = "fail";

    public static void resetState(){
        contract = null;
        holes = new ArrayList<>();
        testCaseManager = null;
        synthesisSpecNode = null;
    }

    public int getMaxTestCaseK() {
        return testCaseManager.getMaxK();
    }

    public Program getSynthesizedProgram() {
        return synthesizedProgram;
    }

    public ArrayList<Hole> getHoles() {
        return holes;
    }

    public NodeRepairKey getSynNodeKey() {
        return synNodeKey;
    }

    public String toString() {
        return synthesizedProgram.toString();
    }


    protected Node createCheckSpecNode(Node synthesisSpecNode) {
        String id = CHECKSPECNODE;
        List<VarDecl> inputs = createCheckSpecInput(synthesisSpecNode.inputs);
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


    /**
     * This creates a new program with the new main that now exists in in the synthesis program.
     *
     * @return
     */
    protected Program makeNewProgram(boolean isMinimal) {

        Node oldMain = synthesizedProgram.getMainNode();
        Node newMain = changeMainNode(oldMain, isMinimal);

        ArrayList<Node> nodes = new ArrayList<>();
        nodes.addAll(synthesizedProgram.nodes);
        int mainIndex = nodes.indexOf(oldMain);

        nodes.set(mainIndex, newMain);

        return new Program(Location.NULL, synthesizedProgram.types, synthesizedProgram.constants, synthesizedProgram
                .functions, nodes, null, "main");
    }

    /**
     * This creates a new program by changing the main to a new main that contains the test case being generated using the counterExampleManager
     */

    private Node changeMainNode(Node mainNode, boolean minimal) {

        List<VarDecl> locals = new ArrayList<>();
        locals.addAll(testCaseManager.testCallVars);
        locals.addAll(testCaseManager.testInputVars);

        List<Equation> equations = new ArrayList<>();
        equations.addAll(testCaseManager.testInputEqs);
        equations.addAll(testCaseManager.testCallEqs);
        equations.add(testCaseManager.propertyEq);

        if (minimal) {
            locals.add(new VarDecl("fixedRout", NamedType.BOOL));
            locals.add(new VarDecl("rPrimeOut", NamedType.BOOL));

            Equation fixedRoutEq = findEqWithLhs(mainNode.equations, "fixedRout");
            Equation rPrimeOut = findEqWithLhs(mainNode.equations, "rPrimeOut");

            equations.add(fixedRoutEq);
            equations.add(rPrimeOut);
        }
        return new Node(mainNode.id, mainNode.inputs, mainNode.outputs, locals, equations, mainNode.properties, mainNode.assertions, mainNode.realizabilityInputs, mainNode.contract, mainNode.ivc);
    }


    /*private Node changeMinimalMainNode(Node mainNode) {
        int currentIndex = testCaseManager.testCallVars.size();

        List<VarDecl> locals = new ArrayList<>(mainNode.locals);
        locals.add(testCaseManager.testCallVars.get(currentIndex));

        locals = addAllIfNotExists(locals, testCaseManager.testInputVars);

        List<Equation> equations = removeEqWithLhs(mainNode.equations, "fail");

        equations.add(testCaseManager.testInputEqs.get(currentIndex));
        equations.addAll(testCaseManager.testCallEqs);
        equations.add(testCaseManager.propertyEq);

        return new Node(mainNode.id, mainNode.inputs, mainNode.outputs, locals, equations, mainNode.properties, mainNode.assertions, mainNode.realizabilityInputs, mainNode.contract, mainNode.ivc);
    }

    private List<VarDecl> addAllIfNotExists(List<VarDecl> locals, List<VarDecl> testInputVars) {
        for (VarDecl var : testInputVars) {
            if (!locals.contains(var))
                locals.add(var);
        }
        return locals;
    }
*/

    /**
     * This creates the H (Historically node).
     *
     * @return
     */
    public Node getGloballyNode() {
        VarDecl inVarDecl = new VarDecl("in", NamedType.BOOL);
        VarDecl outVarDecl = new VarDecl("out", NamedType.BOOL);

        IdExpr inVarExpr = DiscoveryUtil.varDeclToIdExpr(inVarDecl);
        IdExpr outVarExpr = DiscoveryUtil.varDeclToIdExpr(outVarDecl);


        String id = H_discovery;
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
     * This is called to freeze a single hole of interest
     *
     * @return
     */
    protected Expr makeFreezeSingleAssertion(String holeName) {
        BinaryExpr currentEqPreExr = new BinaryExpr(new IdExpr(holeName), BinaryOp.EQUAL, new UnaryExpr(UnaryOp.PRE, new IdExpr(holeName)));
        BinaryExpr assertion = new BinaryExpr(new BoolExpr(true), BinaryOp.ARROW, currentEqPreExr);
        return assertion;
    }


    /**
     * This method is used to find enteries that contains holes, it uses the name of the variable to fetch these
     * enteries.
     * TODO:I need to have another mechanisim than just counting on the name of the variable.
     *
     * @param allIputs
     * @return
     */
    protected List<VarDecl> extractHoleEnteries(List<VarDecl> allIputs) {
        List<VarDecl> holeEnteries = new ArrayList<>();
        for (int i = 0; i < allIputs.size(); i++) {
            if (allIputs.get(i).toString().contains("hole"))
                holeEnteries.add(allIputs.get(i));
        }
        return holeEnteries;

    }

}
