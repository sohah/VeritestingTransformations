package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeStatus;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.*;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.loopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.IdExprToVarDecl;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil.varDeclToIdExpr;
import static jkind.util.Util.getNodeTable;

/**
 * This is the visitor that creates holes for all input and local variables, where the holes are matched to a pre(original expression) or just the original expression.
 */
public class SpecPreHoleVisitor extends AstMapVisitor {

    //accumulates all the varDeclarations for holes that are defined while visiting a specific node, though an instance of this class.
    private List<VarDecl> holeVarDecl = new ArrayList<>();

    private List<VarDecl> containerVarDecl = new ArrayList<>();

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

    // accumulates all the containers and their old values.
    private static HashMap<HoleContainer, Pair<Ast, Value>> containerToConstMap = new HashMap<>();

    //collects holes defined through all containers.
    private static ArrayList<Hole> definedHoles = new ArrayList<>();

    private NodeRepairKey nodeKey;

    private static Program currentPgm;
    private Node currentNode;
    private Collection<? extends VarDecl> holeHelperVarDecl;

    // this contains the current IdExpr for the equation we are trying to add holes in. In this visitor we should
    // avoid making pre holes for IdExprs that refer to the same definition, this causing algeberic loop.
    private IdExpr currentEqLhs = null;

    public static Set<Hole> getHoles() {
        return new HashSet<>(definedHoles);
    }

    public static Set<HoleContainer> getContainers() {
        return containerToConstMap.keySet();
    }


    public void setNodeTable(Map<String, Node> nodeTable) {
        SpecPreHoleVisitor.nodeTable = nodeTable;
    }


    //TODO: needs to be supported
    @Override
    public Expr visit(UnaryExpr e) {

        if ((e.expr instanceof IdExpr) && (e.op == UnaryOp.PRE)) {
            if (!e.expr.toString().equals(currentEqLhs.toString())) {

                NamedType type = NamedType.get((DiscoveryUtil.lookupExprType(e.expr, currentNode, currentPgm)).toString());


                ArrayList<Hole> holes = new ArrayList<>();
                ConstantHole hole1 = new ConstantHole("", NamedType.BOOL);
                ConstantHole hole2 = new ConstantHole("", type);


                holes.add(hole1);
                holes.add(hole2);

                this.holeVarDecl.add(IdExprToVarDecl(hole1, hole1.myType));
                holeVarDecl.add(IdExprToVarDecl(hole2, hole2.myType));

                return createAndPopulateHole(e, type, holes);
            } else
                return e;
        } else {
            Expr expr = e.expr.accept(this);
            if (e.expr == expr) {
                return e;
            }
            return new UnaryExpr(e.location, e.op, expr);
        }

    }


    @Override
    public Expr visit(IdExpr e) {

        if (!e.toString().equals(currentEqLhs.toString())) {
            NamedType type = NamedType.get((DiscoveryUtil.lookupExprType(e, currentNode, currentPgm))
                    .toString());


            ArrayList<Hole> holes = new ArrayList<>();

            ConstantHole hole1 = new ConstantHole("", NamedType.BOOL);
            ConstantHole hole2 = new ConstantHole("", type);

            holes.add(hole1);
            holes.add(hole2);
            holeVarDecl.add(IdExprToVarDecl(hole1, hole1.myType));
            holeVarDecl.add(IdExprToVarDecl(hole2, hole2.myType));

            return createAndPopulateHole(e, type, holes);
        } else
            return e;
    }

    @Override
    public Expr visit(NodeCallExpr e) {

        Node nodeDefinition = nodeTable.get(e.node);
        if (nodeKey.getStatus(nodeDefinition.id) == NodeStatus.REPAIR) {
            Node holeNode = SpecPreHoleVisitor.execute(nodeDefinition, this.nodeKey);
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
            SpecPreHoleVisitor.execute(nodeDefinition, this.nodeKey);
            return new NodeCallExpr(e.location, e.node, visitExprs(e.args));
        }
    }


    @Override
    public Equation visit(Equation e) {
        // Do not traverse e.lhs since they do not really act like Exprs
        currentEqLhs = e.lhs.get(0);
        Expr newRhs = e.expr.accept(this);
        currentEqLhs = null;

        return new Equation(e.location, e.lhs, newRhs);
    }


    @Override
    protected List<Equation> visitEquations(List<Equation> es) { // only visit to replace equations whose number are included in the Config.equationNumToRepair
        List<Equation> holeEquations = new ArrayList<>();
        Iterator<Equation> equationItr = es.iterator();
        int i = 0;
        while (equationItr.hasNext()) {
            Equation equation = equationItr.next();
            if (Config.allEqRepair || Arrays.asList(Config.equationNumToRepair).indexOf(i) >= 0)  //finds if this current equation is an equation we want to create holes in.
                holeEquations.add(visit(equation));
            else holeEquations.add(equation);
            ++i;
        }
        return holeEquations;
    }


    @Override
    public Node visit(Node e) {
        Node oldNode = currentNode;
        this.currentNode = e;

        List<VarDecl> outputs = e.outputs;
        List<VarDecl> locals = new ArrayList<>();
        locals.addAll(e.locals);
        List<String> ivc = e.ivc;
        List<String> realizabilityInputs = e.realizabilityInputs;
        Contract contract = e.contract;
        List<Expr> assertions;
        List<String> properties;
        List<VarDecl> inputs = new ArrayList<>();

        List<Equation> equations;
        if (nodeKey.getStatus(e.id) == NodeStatus.REPAIR) {
            equations = visitEquations(e.equations);
            equations.addAll(getHelperEqs());       //adding equations for helpers

            inputs.addAll(e.inputs);
            inputs.addAll(this.holeVarDecl);
            locals.addAll(getHoleContainerVarDecl());

            assertions = visitAssertions(e.assertions);

//            assertions.addAll(getHolesConstraints());   //adding constraints on holes

            properties = visitProperties(e.properties);


        } else {
            equations = e.equations;
            inputs = e.inputs;
            assertions = e.assertions;
            properties = e.properties;
        }
        this.currentNode = oldNode;

        return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                realizabilityInputs, contract, ivc);
    }

    private Expr createAndPopulateHole(Expr e, NamedType type, ArrayList<Hole> holes) {
        HoleContainer holeContainer = new PreHoleContainer("", type, e, holes);
        containerToConstMap.put(holeContainer, new Pair(e, null));
        VarDecl containerVarDecl = IdExprToVarDecl(holeContainer, type);

        if (loopCount == 0) { //initial run, then setup the holes.
            for (int i = 0; i < holes.size(); i++) {
                //DiscoverContract.holeRepairState.createNewHole(holes.get(i), e, ((ConstantHole) holes.get(i)).myType);
                definedHoles.add(holes.get(i));
            }
        }

        DiscoverContract.holeRepairState.createNewHole(holeContainer, e, holeContainer.myType);

        this.containerVarDecl.add(containerVarDecl);
        return holeContainer;
    }


    /**
     * This executes the ConstHoleVisitor on the main node, which might later invoke multiple instances of the ConstHoleVisitor but on other nodes, where the later requires the other execute methode.
     *
     * @param program
     * @param originalNodeKey
     * @return
     */
    public static Program executeMain(Program program, NodeRepairKey originalNodeKey) {
        Map<String, Node> nodeTable = getNodeTable(program.nodes);

        SpecPreHoleVisitor.currentPgm = program;
        SpecPreHoleVisitor preHoleVisitor = new SpecPreHoleVisitor();
        preHoleVisitor.nodeKey = originalNodeKey;

        preHoleVisitor.setNodeTable(nodeTable);
        Node mainNode = program.getMainNode();
        Ast holeNode = mainNode.accept(preHoleVisitor);

        assert (holeNode instanceof Node);

        holeTable.put(((Node) holeNode).id, (Node) holeNode);
        nodeHoleVarDecl.put(((Node) holeNode).id, preHoleVisitor.holeVarDecl);

        ArrayList<Node> programNodes = new ArrayList<Node>(holeTable.values());
        programNodes.addAll(nonRepairNodes);

        return new Program(Location.NULL, program.types, program.constants, program.functions, programNodes, null,
                mainNode.id);
    }


    /**
     * This is used to execute the ConstHoleVisitor on non-main nodes. i.e, nodes that are called.
     *
     * @param node
     * @return
     */
    public static Node execute(Node node, NodeRepairKey originalNodeKey) {

        SpecPreHoleVisitor specPreHoleVisitor = new SpecPreHoleVisitor();
        specPreHoleVisitor.nodeKey = originalNodeKey;

        if (DiscoverContract.userSynNodes.contains(node.id)) {
            if (holeTable.containsKey(node.id)) //if we already changed the node with constant holes then just return that.
                return holeTable.get(node.id);


            Ast holeNode = node.accept(specPreHoleVisitor);

            assert (holeNode instanceof Node);

            holeTable.put(((Node) holeNode).id, (Node) holeNode);
            nodeHoleVarDecl.put(((Node) holeNode).id, specPreHoleVisitor.holeVarDecl);
            return (Node) holeNode;
        } else { //adding the node in its non-repair form because it is not defined by the user to being of interest to repair.
            if (!nonRepairNodes.contains(node))
                nonRepairNodes.add(node);
            return (Node) node.accept(specPreHoleVisitor);
        }

    }

    public Collection<? extends Expr> getHolesConstraints() {
        ArrayList<Expr> holesConstraints = new ArrayList<>();
        Set<Hole> holes = SpecPreHoleVisitor.getHoles();

        Iterator<Hole> itr = holes.iterator();
        while (itr.hasNext()) {
            Hole hole = itr.next();

            assert (hole instanceof PreHoleContainer);

            holesConstraints.add(((PreHoleContainer) hole).getContainerFreezeAssertion());
        }
        return holesConstraints;
    }

    public ArrayList<Equation> getHelperEqs() {
        ArrayList<Equation> containerEqs = new ArrayList<>();
        Set<HoleContainer> containers = SpecPreHoleVisitor.getContainers();

        Iterator<HoleContainer> itr = containers.iterator();
        while (itr.hasNext()) {
            HoleContainer container = itr.next();

            assert (container instanceof PreHoleContainer);

            containerEqs.add(((PreHoleContainer) container).getContainerEquation());
        }
        return containerEqs;

    }

    public Collection<? extends VarDecl> getHoleContainerVarDecl() {
        ArrayList<VarDecl> containerVarDecls = new ArrayList<>();
        Set<HoleContainer> containers = SpecPreHoleVisitor.getContainers();


        Iterator<HoleContainer> itr = containers.iterator();
        while (itr.hasNext()) {
            HoleContainer container = itr.next();

            assert (container instanceof PreHoleContainer);

            containerVarDecls.add(((PreHoleContainer) container).getContainerVarDecl());
        }

        return containerVarDecls;
    }
}
