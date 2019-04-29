package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.repair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.RepairMode;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.PreHoleContainer;
import jkind.lustre.*;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.TNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.findNode;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeStatus.REPAIR;

/**
 * This visitor puts back the values of the holes into the specification of T.
 */

public class ConstPluggerVisitor extends AstMapVisitor {
    private final Program counterExamplePgm;
    private final Program synthesisPgm;


    public ConstPluggerVisitor(Program counterExamplePgm, Program synthesisPgm) {
        this.counterExamplePgm = counterExamplePgm;
        this.synthesisPgm = synthesisPgm;
    }

    @Override
    public Expr visit(IdExpr e) {
        if ((e instanceof ConstantHole) || (e instanceof PreHoleContainer)) {
            Ast repairExpr = DiscoverContract.holeRepairState.getRepairValue((Hole) e);
            assert repairExpr instanceof Expr;
            return (Expr) repairExpr;
        } else
            return e;
    }

    @Override
    protected List<Equation> visitEquations(List<Equation> es) {
        if (Config.repairMode == RepairMode.PRE) {
            List<Equation> repairedEquations = new ArrayList<>();
            Iterator<Equation> equationItr = es.iterator();

            while (equationItr.hasNext()) {
                Equation equation = equationItr.next();
                if (!equation.lhs.toString().contains("container")) { //skip constrainted equations made for containers
                    repairedEquations.add(visit(equation));
                }
            }
            return repairedEquations;
        } else
            return map(this::visit, es);
    }


    /**
     * uses the synthesisPgm to find the VarDecl of the hole and returns that.
     *
     * @param e
     * @return
     */
    private VarDecl getHoleVarDecl(IdExpr e) {
        List<VarDecl> inputs = synthesisPgm.getMainNode().inputs;
        for (int i = 0; i < inputs.size(); i++) {
            if (inputs.get(i).id.equals(e.id)) {
                VarDecl myVarDecl = inputs.get(i);
                return myVarDecl;
            }
        }
        System.out.println("unable to find the VarDecl for a variable.");
        assert false;
        return null;
    }

    private Expr translateValueToExpr(Value value, VarDecl holVarDecl) {
        return DiscoveryUtil.valueToExpr(value, holVarDecl.type);

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
        //if it is the T_node we need to have the old property from the counterExample form, otherwise we proceed with what we have from the repaired spec.
        List<String> properties = (e.id.equals(TNODE)) ? visitProperties(oldSpecNode.properties) : visitProperties(e.properties);
        List<String> ivc = visitIvc(oldSpecNode.ivc);
        List<String> realizabilityInputs = visitRealizabilityInputs(oldSpecNode.realizabilityInputs);
        Contract contract = visit(oldSpecNode.contract);
        return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                realizabilityInputs, contract, ivc);
    }


    public static Program execute(Program counterExamplePgm, Program synthesisPgm, NodeRepairKey nodeRepairKey) {


        List<Node> toRepairNodes = getToRepairNodes(counterExamplePgm, nodeRepairKey);
        List<Node> repairedNodes = new ArrayList<>();

        ConstPluggerVisitor constPluggerVisitor = new ConstPluggerVisitor(counterExamplePgm, synthesisPgm);

        for (int i = 0; i < toRepairNodes.size(); i++) {
            Node holeNode = findNode(synthesisPgm.nodes, toRepairNodes.get(i));
            if (holeNode != null) {//a node that is in the spec but not really used, i.e, called. So it is not part of the synthesis.
                Ast repairedHole = holeNode.accept(constPluggerVisitor);
                assert (repairedHole instanceof Node);
                repairedNodes.add((Node) repairedHole);
            }
        }

        List<Node> repairedPgmNodes = replaceOldNodes(counterExamplePgm, repairedNodes, nodeRepairKey);

        return new Program(Location.NULL, counterExamplePgm.types, counterExamplePgm.constants, counterExamplePgm
                .functions, repairedPgmNodes, null, counterExamplePgm.main);
    }

    private static List<Node> replaceOldNodes(Program counterExamplePgm, List<Node> repairedNodes, NodeRepairKey nodeRepairKey) {
        List<Node> newNodes = new ArrayList<>();
        List<Node> oldNodes = counterExamplePgm.nodes;
        for (int i = 0; i < oldNodes.size(); i++) {
            Node oldNode = oldNodes.get(i);
            if (!(nodeRepairKey.getStatus(oldNode.id) == REPAIR))
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
     * @param nodeRepairKey
     * @return
     */
    private static List<Node> getToRepairNodes(Program program, NodeRepairKey nodeRepairKey) {
        List<Node> toRepairNodes = new ArrayList<>();
        List<Node> allNodes = program.nodes;
        for (int i = 0; i < allNodes.size(); i++) {
            Node node = allNodes.get(i);
            //if (isSpecNode(node))
            if (nodeRepairKey.getStatus(node.id) == REPAIR) //repair if the user has specified it to be a repair node.
                toRepairNodes.add(node);
        }
        return toRepairNodes;
    }
}
