package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.*;
import jkind.lustre.parsing.LustreParseUtil;
import jkind.results.InvalidProperty;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.renameMainNode;

public class SynthesisContract {

    public final Program synthesisProgram;
    public final Contract contract;

    public SynthesisContract(gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract contract, String fileName) throws IOException {
        this.contract = contract;
        Program holeProgram = ConstHoleVisitor.executeMain(LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(fileName)
        ), "UTF-8")));

        List<TypeDef> types = holeProgram.types;
        List<Constant> constants = holeProgram.constants;
        List<Function> functions = holeProgram.functions;
        List<Node> nodes = new ArrayList<>();
        nodes.addAll(holeProgram.nodes);
        nodes.add(getGloballyNode());
        String main = holeProgram.main;

        Node mainNode = holeProgram.getMainNode();
        Node synthesisSpecNode = renameMainNode(DiscoverContract.SYNTHESISNODE, mainNode);

        nodes.set(nodes.indexOf(mainNode), synthesisSpecNode);

        nodes.add(createCheckSpecNode(synthesisSpecNode));

        nodes.add(createSynthesisMain(synthesisSpecNode));

        synthesisProgram = new Program(holeProgram.location, types, constants, functions, nodes, "main");

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

        NodeCallExpr thenStmt = new NodeCallExpr(DiscoverContract.SYNTHESISNODE, (ArrayList<Expr>)(ArrayList<?>)DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.inputs));

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


        List<Equation> myEquations = callHoleEquation(synthesisSpecNode);
        List<String> myProperties = null;


        return new Node("main", synthesisSpecNode.inputs, synthesisSpecNode.outputs, synthesisSpecNode.locals, myEquations, myProperties, myAssertions, synthesisSpecNode.realizabilityInputs, synthesisSpecNode.contract, synthesisSpecNode.ivc);
    }

    private List<Equation> callHoleEquation(Node synthesisSpecNode) {
        List<Equation> myEquations = new ArrayList<>();

        //we are not expecting anything as an output except just ok.
        assert (synthesisSpecNode.outputs.size() == 1);

        IdExpr lhs = DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.outputs.get(0));
        List<IdExpr> rhsParameters = DiscoveryUtil.varDeclToIdExpr(synthesisSpecNode.inputs);
        NodeCallExpr rhs = new NodeCallExpr(DiscoverContract.SYNTHESISNODE, (ArrayList<Expr>) (ArrayList<?>) rhsParameters);

        Equation myEquation = new Equation(lhs, rhs);
        myEquations.add(myEquation);

        return myEquations;
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


    public static void collectCounterExample(JKindResult counterExResult, Contract contract) {
        for (PropertyResult pr : counterExResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                System.out.println(ip.getCounterexample());
            }
        }
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
}
