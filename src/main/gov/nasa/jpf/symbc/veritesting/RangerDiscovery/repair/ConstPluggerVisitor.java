package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.Hole;
import jkind.lustre.*;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.findNode;

/**
 * This visitor puts back the values of the holes into the specification of T.
 */

public class ConstPluggerVisitor extends AstMapVisitor {
    private final Program counterExamplePgm;
    private final Program synthesisPgm;

    HashMap<Hole, Value> holeSynValuesMap;


    public ConstPluggerVisitor(HashMap<Hole, Value> holeSynValuesMap, Program counterExamplePgm, Program synthesisPgm) {
        this.holeSynValuesMap = holeSynValuesMap;
        this.counterExamplePgm = counterExamplePgm;
        this.synthesisPgm = synthesisPgm;
    }

    @Override
    public Expr visit(IdExpr e) {
        if (e instanceof ConstantHole) {
            Value value = holeSynValuesMap.get(e);
            return translateValueToExpr(value);
        } else
            return e;
    }

    private Expr translateValueToExpr(Value value) {
        if (value instanceof BooleanValue)
            return new BoolExpr(((BooleanValue) value).value);
        else if (value instanceof IntegerValue)
            return new IntExpr(((IntegerValue) value).value);
        else {
            System.out.println("unsupported values type");
            assert false;
            return null;
        }
    }


    @Override
    public Expr visit(NodeCallExpr e) {
        List<Expr> newArgs = new ArrayList<>();
        for (int i = 0; i < e.args.size(); i++) {
            if (!e.args.toString().contains("hole"))
                newArgs.add((e.args.get(i).accept(this)));
        }
        return new NodeCallExpr(e.location, e.node, visitExprs(e.args));
    }


    @Override
    public Node visit(Node e) {
        Node oldSpecNode = findNode(counterExamplePgm.nodes, e);
        List<VarDecl> inputs = visitVarDecls(oldSpecNode.inputs);
        List<VarDecl> outputs = visitVarDecls(oldSpecNode.outputs);
        List<VarDecl> locals = visitVarDecls(oldSpecNode.locals);
        List<Equation> equations = visitEquations(e.equations);
        List<Expr> assertions = visitAssertions(e.assertions);
        List<String> properties = visitProperties(e.properties);
        List<String> ivc = visitIvc(oldSpecNode.ivc);
        List<String> realizabilityInputs = visitRealizabilityInputs(oldSpecNode.realizabilityInputs);
        Contract contract = visit(oldSpecNode.contract);
        return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                realizabilityInputs, contract, ivc);
    }


    public static Program execute(HashMap<Hole, Value> holeSynValuesMap, Program counterExamplePgm, Program synthesisPgm) {


        List<Node> toRepairNodes = getToRepairNodes(counterExamplePgm);
        List<Node> repairedNodes = new ArrayList<>();

        ConstPluggerVisitor constPluggerVisitor = new ConstPluggerVisitor(holeSynValuesMap, counterExamplePgm, synthesisPgm);

        for (int i = 0; i < toRepairNodes.size(); i++) {
            Node holeNode = findNode(synthesisPgm.nodes, toRepairNodes.get(i));
            if (holeNode != null) {//a node that is in the spec but not really used, i.e, called. So it is not part of the synthesis.
                Ast repairedHole = holeNode.accept(constPluggerVisitor);
                assert (repairedHole instanceof Node);
                repairedNodes.add((Node) repairedHole);
            }
        }

        List<Node> repairedPgmNodes = replaceOldNodes(counterExamplePgm, repairedNodes);

        return new Program(Location.NULL, counterExamplePgm.types, counterExamplePgm.constants, counterExamplePgm.functions, repairedPgmNodes, counterExamplePgm.main);
    }

    private static List<Node> replaceOldNodes(Program counterExamplePgm, List<Node> repairedNodes) {
        List<Node> newNodes = new ArrayList<>();
        List<Node> oldNodes = counterExamplePgm.nodes;
        for (int i = 0; i < oldNodes.size(); i++) {
            Node oldNode = oldNodes.get(i);
            if (!needsRepairNode(oldNode))
                newNodes.add(oldNode);
            else { // return the corresponding repaired node.
                Node repairedNode = findNode(repairedNodes, oldNode);
                if (repairedNode != null) //nodes can be null if they are not called from the spec node, i.e., a node that is never used is never bothered to repair or include in the list of nodes, and thus we might get a null if we ever looked for it. Another way is to assert that these null node are in the nodes that have not been included in the repair, this is neater and less error prone.
                    newNodes.add(repairedNode);
            }
        }
        return newNodes;
    }


    /**
     * finds the spec nodes that we need to repair
     *
     * @param program
     * @return
     */
    private static List<Node> getToRepairNodes(Program program) {
        List<Node> toRepairNodes = new ArrayList<>();
        List<Node> allNodes = program.nodes;
        for (int i = 0; i < allNodes.size(); i++) {
            Node node = allNodes.get(i);
            //if (isSpecNode(node))
            if (DiscoverContract.userSynNodes.contains(node.id)) //repair if the user has specified it to be a repair node.
                toRepairNodes.add(node);
        }
        return toRepairNodes;
    }

    private static boolean needsRepairNode(Node node) {
        String nodeName = node.id;
        if (nodeName.equals("main") || nodeName.equals(DiscoverContract.WRAPPERNODE) || nodeName.equals(DiscoverContract.RNODE))
            return false;
        else
            return true;
    }

}
