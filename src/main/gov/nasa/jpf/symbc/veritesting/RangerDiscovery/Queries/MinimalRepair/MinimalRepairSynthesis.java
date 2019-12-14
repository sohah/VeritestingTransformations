package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ARepairSynthesis;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ThereExistsQuery;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.findNodeStr;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.renameNode;


/**
 * This is used to synthize a tighter different repair, using the other part of the query for the forall, we ensure
 * that the repair is actually included in the old repair and is matching the specification.
 */
public class MinimalRepairSynthesis extends ThereExistsQuery {
    private Node lastRepairNode;

    /**
     * initial minimal repair is made from the last known good repair, not test cases yet, just new free variables as
     * well as a fixed node for last known repair.
     *
     * @param aRepairSynthesis
     * @param lastRepairNode
     */
    public MinimalRepairSynthesis(ARepairSynthesis aRepairSynthesis, Node lastRepairNode) {
        //this is the initial synthesized program that we need to update with the new I', O' call.

        this.lastRepairNode = renameNode(FIXED_T, lastRepairNode); //rename it to R so we can call it again
        List<Node> newNodes = createFixedNodePart(aRepairSynthesis.getSynthesizedProgram());
        newNodes.add(this.lastRepairNode); //this adds the constant R that we have found previously
        synNodeKey = aRepairSynthesis.getSynNodeKey();

        Program oldSynthesisPgm = aRepairSynthesis.getSynthesizedProgram();
        Node newMain = createVariableNodePart(oldSynthesisPgm);

        newNodes.add(newMain);

        synthesizedProgram = new Program(oldSynthesisPgm.location, oldSynthesisPgm.types, oldSynthesisPgm
                .constants, oldSynthesisPgm
                .functions, newNodes, null, "main");
    }

    private Node createVariableNodePart(Program synthesizedProgram) {
        Node existingMain = synthesizedProgram.getMainNode();
        Node updatedMain = createSynthesisMain(existingMain);
        return updatedMain;
    }


    /**
     * For this ThereExists query we need the fixed part is defined exactly ast the synthesized program except for the main which is considered as a variable part. Therefore at this point we create the fixed part only that does not contain the main node.
     *
     * @param holeProgram
     * @return
     */
    @Override
    protected List<Node> createFixedNodePart(Program holeProgram) {
        Node mainNode = holeProgram.getMainNode();

        List noMainNodes = new ArrayList<>(holeProgram.nodes);
        noMainNodes.remove(mainNode);

        return noMainNodes;
    }


    @Override
    protected Pair<List<VarDecl>, List<Equation>> createCheckSpeckLocals(Node synthesisSpecNode) {
        return null;
    }

    /**
     * This creates the variable part which is the main, based on the test cases generated, in the first step we have no counter Example yet, thus this is not called/used in the initial creation of R'
     *
     * @param counterExResult
     * @return
     */
    @Override
    protected Node createVariableNodePart(JKindResult counterExResult) {
        assert false; //not yet implemented
        return null;
    }

    @Override
    protected List<VarDecl> createCheckSpecInput(List<VarDecl> synthesisInputs) {
        assert false; //not yet implemented
        return null;
    }

    /**
     * It takes a main of the original synthesized program, and changes it to contain the new free input and output vars, as well as the calls to the R and to checkspec (which we call the R'). It uses the definitions of the lastRepairNode to make the variables bindings.
     *
     * @param exisingMain
     * @return
     */
    @Override
    protected Node createSynthesisMain(Node exisingMain) {
        List<VarDecl> freeInputOutputDecl = this.lastRepairNode.inputs;


        //these are the inputs that are going to be passed to FixedR, there we do not need any holes passed
        List<VarDecl> rInputs = new ArrayList<>(freeInputOutputDecl);

        //input parameters of the main, are all the input in the synthesis, which should be the holes as well as the
        // new I',O' that we want to create to bind R and R'
        List<VarDecl> allInputs = new ArrayList<>(freeInputOutputDecl);
        allInputs.addAll(exisingMain.inputs);


        List<Expr> freeExpArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(rInputs);

        // R here is the fixed R that we discovered.
        List<VarDecl> locals = new ArrayList<>(exisingMain.locals);
        VarDecl outputOfRCallVar = new VarDecl("fixedRout", NamedType.BOOL);
        VarDecl outputOfRPrimeCallVar = new VarDecl("rPrimeOut", NamedType.BOOL);
        locals.add(outputOfRCallVar);
        locals.add(outputOfRPrimeCallVar);


        List<Equation> equations = new ArrayList<>(exisingMain.equations);
        IdExpr outputOfRCallExp = DiscoveryUtil.varDeclToIdExpr(outputOfRCallVar);
        IdExpr outputOfRPrimeCallExp = DiscoveryUtil.varDeclToIdExpr(outputOfRPrimeCallVar);

        //creating the call to the fixed R
        NodeCallExpr callR = new NodeCallExpr(FIXED_T, freeExpArgs);
        Equation rCallEq = new Equation(outputOfRCallExp, callR);
        equations.add(rCallEq);


        //creating the call to the current checkspec which we refer to as R'
        List actualExpArgsCheckSpec = new ArrayList();
        actualExpArgsCheckSpec.addAll(freeExpArgs);
        actualExpArgsCheckSpec.addAll(holes);
        //actualExpArgsCheckSpec.add(new IntExpr(getMaxTestCaseK() - 1));
        NodeCallExpr callTnode = new NodeCallExpr(TNODE, actualExpArgsCheckSpec);
        Equation tNodeCall = new Equation(outputOfRPrimeCallExp, callTnode);
        equations.add(tNodeCall); // to find the R'

        //creating the equation of the property we want to check.
        equations = makeNewFailPropEqs(outputOfRCallExp, outputOfRPrimeCallExp, equations);


        return new Node("main", allInputs, exisingMain.outputs, locals, equations, exisingMain.properties, exisingMain
                .assertions, exisingMain
                .realizabilityInputs, exisingMain.contract, exisingMain.ivc);
    }

    /**
     * finds the fail equation and replaces its condition with R and !R', where R' is the output of the checkspec
     * It also updates the list of equations to have the updated fail eq instead of the old one.
     *
     * @param outputOfRCallExp
     * @param outputOfRPrimeCallExp
     * @param equations
     * @return
     */
    private List<Equation> makeNewFailPropEqs(IdExpr outputOfRCallExp, IdExpr outputOfRPrimeCallExp, List<Equation>
            equations) {

        List<Equation> newEquations = new ArrayList<>(equations);
        //oldFailEq should be in the form of unary not, with a bunch of conjunct ok expressions.
        Equation oldFailEq = DiscoveryUtil.findEqInList(newEquations, FAIL);
        newEquations.remove(oldFailEq);

        assert oldFailEq.lhs.size() == 1;
        assert oldFailEq.expr instanceof UnaryExpr;
        assert ((UnaryExpr) oldFailEq.expr).op.equals(UnaryOp.NOT);
        // not(ok and R and !R')
        Expr newProperty = new BinaryExpr(outputOfRCallExp, BinaryOp.AND, new UnaryExpr(UnaryOp.NOT,
                outputOfRPrimeCallExp));
        newProperty = new BinaryExpr(((UnaryExpr) oldFailEq.expr).expr, BinaryOp
                .AND, newProperty);
        newProperty = new UnaryExpr(UnaryOp.NOT, newProperty);
        Equation newFailEq = new Equation(oldFailEq.lhs, newProperty);
        newEquations.add(newFailEq);
        return newEquations;
    }

    public void collectCounterExample(JKindResult counterExampleResult, Node lastSynMainNode) {
        testCaseManager.collectCounterExampleMinimal(counterExampleResult, lastSynMainNode);
        synthesizedProgram = makeNewProgram(true);
    }

    //have the side effect of changing its internal synthesized program to the new known repair node.
    public void changeFixedR(Node newMain) {
        List newNodes = new ArrayList<>(synthesizedProgram.nodes);
        Node oldKnownRepairNode = findNodeStr(synthesizedProgram.nodes, FIXED_T);
        newNodes.remove(oldKnownRepairNode); // removing the old main node;
        Node newFixedT = renameNode(FIXED_T, newMain);
        newNodes.add(newFixedT); //adding the new main
        synthesizedProgram = new Program(synthesizedProgram.location, synthesizedProgram.types, synthesizedProgram.constants, synthesizedProgram.functions, newNodes, null, synthesizedProgram.main);

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
