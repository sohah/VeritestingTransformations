package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

    //this defines the varDecl associated with every nodeHole
    private static Map<String, List<VarDecl>> nodeHoleVarDecl = new HashMap<>();

    // accumulates all the holes and the old constant value that they are replacing.
    private static Map<Hole, Ast> holeToConstatnt = new HashMap<>();


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

        Node holeNode = ConstHoleVisitor.execute(nodeTable.get(e.node));
        List<Expr> arguments = visitExprs(e.args);
        List<VarDecl> callHoles = nodeHoleVarDecl.get(holeNode.id);

        arguments.addAll(varDeclToIdExpr(callHoles));


        /**
         * sort of a hack here, but should work. this is handling the case were the called node has already been called and therefore we have already included its holes in the previous call. Here we are checking that the first hole in the call exist instead of checking all of them.
         */

        if (!holeVarDecl.contains(callHoles.get(0)))
            holeVarDecl.addAll(callHoles);

        //return new NodeCallExpr(e.location, e.node, arguments);

        return new FunctionCallExpr(e.location, e.node, arguments);
    }

    @Override
    public Node visit(Node e) {
        List<VarDecl> outputs = e.outputs;
        List<VarDecl> locals = e.locals;
        List<Equation> equations = visitEquations(e.equations);

        List<VarDecl> inputs = new ArrayList<>();
        inputs.addAll(e.inputs);
        inputs.addAll(this.holeVarDecl);

        List<Expr> assertions = visitAssertions(e.assertions);
        List<String> properties = visitProperties(e.properties);
        List<String> ivc = e.ivc;
        List<String> realizabilityInputs = e.realizabilityInputs;
        Contract contract = e.contract;
        return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                realizabilityInputs, contract, ivc);
    }

    private Expr createAndPopulateHole(Expr e, NamedType type) {
        ConstantHole newHole = new ConstantHole("");
        holeToConstatnt.put(newHole, e);
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

        return new Program(Location.NULL, program.types, program.constants, program.functions, programNodes, mainNode.id);
    }


    /**
     * This is used to execute the ConstHoleVisitor on non-main nodes.
     *
     * @param node
     * @return
     */
    public static Node execute(Node node) {

        if (holeTable.containsKey(node.id)) //if we already changed the node with constant holes then just return that.
            return holeTable.get(node.id);

        ConstHoleVisitor constHoleVisitor = new ConstHoleVisitor();
        Ast holeNode = node.accept(constHoleVisitor);

        assert (holeNode instanceof Node);

        holeTable.put(((Node) holeNode).id, (Node) holeNode);
        nodeHoleVarDecl.put(((Node) holeNode).id, constHoleVisitor.holeVarDecl);
        return (Node) holeNode;

    }

}
