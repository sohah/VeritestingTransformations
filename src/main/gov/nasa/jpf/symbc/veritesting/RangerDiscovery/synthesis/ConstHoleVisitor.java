package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.IdExprToVarDecl;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.varDeclToIdExpr;
import static jkind.util.Util.getNodeTable;

/**
 * This is the visitor that creates holes for all contants in the nodes. It starts by the main and if it found a reference to another node, then it does that and comes back. If a node that have a holes defined in it and was called by some another node, then in the signature of the call and also in the declartion of the parameters of the outside node, needs to include those holes which are defined in the inner node.
 */
public class ConstHoleVisitor extends AstMapVisitor {

    //accumulates all the varDeclarations for holes that are defined while visiting a specific node, though an instance of this class.
    private List<VarDecl> holeVarDecl = new ArrayList<>();

    //original nodes before replacing constants with holes.
    private static Map<String, Node> nodeTable;

    //nodes after they have been changed to holes instead of constants, this table is incrementally populated.
    private static Map<String, Node> holeTable = new HashMap<>();

    /**
     * This carries the nodes that are called from a hole node, but itself is not defined by the user to be repaired.
     */
    private static List<Node> nonRepairNodes = new ArrayList<>();

    //this defines the varDecl associated with every nodeHole
    private static Map<String, List<VarDecl>> nodeHoleVarDecl = new HashMap<>();

    // accumulates all the holes and the old constant value that they are replacing.
    private static HashMap<Hole, Pair<Ast, Value>> holeToConstantMap = new HashMap<>();

    public static Set<Hole> getHoles() {
        return holeToConstantMap.keySet();
    }

    public static HashMap<Hole, Pair<Ast, Value>> getHoleToConstant() {
        return holeToConstantMap;
    }

    public void setNodeTable(Map<String, Node> nodeTable) {
        ConstHoleVisitor.nodeTable = nodeTable;
    }


    @Override
    public Expr visit(BoolExpr e) {
        return createAndPopulateHole(e, NamedType.BOOL);
    }


    @Override
    public Expr visit(IntExpr e) {
        return createAndPopulateHole(e, NamedType.INT);
    }

    @Override
    public Expr visit(NodeCallExpr e) {

        Node nodeDefinition = nodeTable.get(e.node);
        if (DiscoverContract.userSynNodes.contains(nodeDefinition.id)) {
            Node holeNode = ConstHoleVisitor.execute(nodeDefinition);
            List<Expr> arguments = visitExprs(e.args);
            List<VarDecl> callHoles = nodeHoleVarDecl.get(holeNode.id);

            arguments.addAll(varDeclToIdExpr(callHoles));


            /**
             * sort of a hack here, but should work. this is handling the case were the called node has already been called and therefore we have already included its holes in the previous call. Here we are checking that the first hole in the call exist instead of checking all of them.
             * This should only be done if the node is indeed a node we want to repair.
             */

            if (!holeVarDecl.contains(callHoles.get(0)))
                holeVarDecl.addAll(callHoles);

            return new NodeCallExpr(e.location, e.node, arguments);
        } else {
            ConstHoleVisitor.execute(nodeDefinition);
            return new NodeCallExpr(e.location, e.node, visitExprs(e.args));
        }
    }

    @Override
    public Node visit(Node e) {
        List<VarDecl> outputs = e.outputs;
        List<VarDecl> locals = e.locals;
        List<String> ivc = e.ivc;
        List<String> realizabilityInputs = e.realizabilityInputs;
        Contract contract = e.contract;
        List<Expr> assertions;
        List<String> properties;
        List<VarDecl> inputs = new ArrayList<>();

        List<Equation> equations;
        if (DiscoverContract.userSynNodes.contains(e.id)) {
            equations = visitEquations(e.equations);
            inputs.addAll(e.inputs);
            inputs.addAll(this.holeVarDecl);

            assertions = visitAssertions(e.assertions);
            properties = visitProperties(e.properties);

        } else {
            equations = e.equations;
            inputs = e.inputs;

            assertions = e.assertions;
            properties = e.properties;
        }
        return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                realizabilityInputs, contract, ivc);
    }

    private Expr createAndPopulateHole(Expr e, NamedType type) {
        ConstantHole newHole = new ConstantHole("");
        holeToConstantMap.put(newHole, new Pair(e, null));
        VarDecl newVarDecl = IdExprToVarDecl(newHole, type);
        this.holeVarDecl.add(newVarDecl);
        return newHole;
    }

    /**
     * This executes the ConstHoleVisitor on the main node, which might later invoke multiple instances of the ConstHoleVisitor but on other nodes, where the later requires the other execute methode.
     *
     * @param program
     * @return
     */
    public static Program executeMain(Program program) {
        Map<String, Node> nodeTable = getNodeTable(program.nodes);

        ConstHoleVisitor constHoleVisitor = new ConstHoleVisitor();
        constHoleVisitor.setNodeTable(nodeTable);
        Node mainNode = program.getMainNode();
        Ast holeNode = mainNode.accept(constHoleVisitor);

        assert (holeNode instanceof Node);

        holeTable.put(((Node) holeNode).id, (Node) holeNode);
        nodeHoleVarDecl.put(((Node) holeNode).id, constHoleVisitor.holeVarDecl);

        ArrayList<Node> programNodes = new ArrayList<Node>(holeTable.values());
        programNodes.addAll(nonRepairNodes);

        return new Program(Location.NULL, program.types, program.constants, program.functions, programNodes, mainNode.id);
    }


    /**
     * This is used to execute the ConstHoleVisitor on non-main nodes. i.e, nodes that are called.
     *
     * @param node
     * @return
     */
    public static Node execute(Node node) {

        ConstHoleVisitor constHoleVisitor = new ConstHoleVisitor();
        if (DiscoverContract.userSynNodes.contains(node.id)) {
            if (holeTable.containsKey(node.id)) //if we already changed the node with constant holes then just return that.
                return holeTable.get(node.id);


            Ast holeNode = node.accept(constHoleVisitor);

            assert (holeNode instanceof Node);

            holeTable.put(((Node) holeNode).id, (Node) holeNode);
            nodeHoleVarDecl.put(((Node) holeNode).id, constHoleVisitor.holeVarDecl);
            return (Node) holeNode;
        } else { //adding the node in its non-repair form because it is not defined by the user to being of interest to repair.
            if (!nonRepairNodes.contains(node))
                nonRepairNodes.add(node);
            return (Node) node.accept(constHoleVisitor);
        }

    }

}
