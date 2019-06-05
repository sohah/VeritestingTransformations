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

/**
 * This visitor puts back the values of the holes into the specification of T.
 */

public class ConstPluggerVisitor extends AstMapVisitor {
    HashMap<Hole, Value> holeSynValuesMap;


    public ConstPluggerVisitor(HashMap<Hole, Value> holeSynValuesMap) {
        this.holeSynValuesMap = holeSynValuesMap;
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

    public static Program execute(HashMap<Hole, Value> holeSynValuesMap, Program counterExamplePgm, Program synthesisPgm) {

        List<Node> toRepairNodes = getToRepairNodes(counterExamplePgm);
        List<Node> repairedSigNodes = repairNodes(toRepairNodes, synthesisPgm); // nodes whose signtures are reapried but not yet their equations.
        ArrayList<Node> repairedNodes = new ArrayList<>();

        ConstPluggerVisitor constPluggerVisitor = new ConstPluggerVisitor(holeSynValuesMap);

        for (int i = 0; i < repairedSigNodes.size(); i++) {
            repairedNodes.add((Node) repairedSigNodes.get(i).accept(constPluggerVisitor));
        }

        List<Node> repairedPgmNodes = replaceOldNodes(counterExamplePgm, repairedNodes);

        return new Program(Location.NULL, counterExamplePgm.types, counterExamplePgm.constants, counterExamplePgm.functions, repairedPgmNodes, counterExamplePgm.main);
    }

    private static List<Node> replaceOldNodes(Program counterExamplePgm, ArrayList<Node> repairedNodes) {
        List<Node> newNodes = new ArrayList<>();
        List<Node> oldNodes = counterExamplePgm.nodes;
        for (int i = 0; i < oldNodes.size(); i++) {
            Node oldNode = oldNodes.get(i);
            if (!isSpecNode(oldNode))
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
     * This gets the nodes that needs repair from the SynthesisProgram and also change everything back to the way it was in the counter example step, except for the equations, which needs to be filled out by the constPluggerVisitor that should take care of that part.
     *
     * @param toRepairNodes
     * @param synthesisPgm
     * @return
     */
    private static List<Node> repairNodes(List<Node> toRepairNodes, Program synthesisPgm) {
        List<Node> repairedSignatureNodes = new ArrayList<>();
        List<Node> synthesisNodes = synthesisPgm.nodes;
        for (int i = 0; i < toRepairNodes.size(); i++) {
            Node nodeToRepair = toRepairNodes.get(i);
            Node synthesisNode = findNode(synthesisNodes, nodeToRepair);
            if (synthesisNode != null) //it can be null if the node was part of the spec but was never really used, i.e., not called.
                repairedSignatureNodes.add(new Node(nodeToRepair.id, nodeToRepair.inputs, nodeToRepair.outputs, nodeToRepair.locals, synthesisNode.equations, nodeToRepair.properties, nodeToRepair.assertions, nodeToRepair.realizabilityInputs, nodeToRepair.contract, nodeToRepair.ivc));
        }
        return repairedSignatureNodes;
    }

    private static Node findNode(List<Node> nodes, Node node) {
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(node.id))
                return nodes.get(i);
        }
        System.out.println("problem finding the node to repair!");
        return null;
    }

    private static List<Node> getToRepairNodes(Program program) {
        List<Node> toRepairNodes = new ArrayList<>();
        List<Node> allNodes = program.nodes;
        for (int i = 0; i < allNodes.size(); i++) {
            Node node = allNodes.get(i);
            if (isSpecNode(node))
                toRepairNodes.add(node);
        }
        return toRepairNodes;
    }

    private static boolean isSpecNode(Node node) {
        String nodeName = node.id;
        if (nodeName.equals("main") || nodeName.equals(DiscoverContract.WRAPPERNODE) || nodeName.equals(DiscoverContract.RNODE))
            return false;
        else
            return true;
    }

}
