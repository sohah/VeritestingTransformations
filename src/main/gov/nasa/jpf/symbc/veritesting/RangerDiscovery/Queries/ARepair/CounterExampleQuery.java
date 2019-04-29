package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ForAllQuery;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.TNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.WRAPPERNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.counterExPropertyName;


/**
 * This class holds the T program, that can be used for either the counter Example step or the synthesis step.
 */
public class CounterExampleQuery extends ForAllQuery {
    public final List<TypeDef> types;
    public final List<Constant> constants;
    public final List<Function> functions;
    public final List<Node> nodes;

    public static Node rNode;
    public static Node rWrapper;
    public static Node mainNode;

    private Program counterExamplePgm;

    /**
     * Generates a T program counter example step from a file path, usually this is done in the first time.
     *
     * @return
     */

    public static void resetState(){
        CounterExampleQuery.rNode = null;
        CounterExampleQuery.rWrapper = null;
        CounterExampleQuery.mainNode = null;
    }

    public CounterExampleQuery(DynamicRegion dynRegion, Program program, Contract contract) {

        //generating rNode and rWrapper

        rNode = ToLutre.generateRnode(dynRegion, contract);
        rWrapper = ToLutre.generateRwrapper(contract.rInOutManager);

        //generating nodes, const, types, etc from the spec

        List<TypeDef> types = new ArrayList<>();
        List<Constant> constants = new ArrayList<>();
        List<Function> functions = new ArrayList<>();
        List<Node> nodes = new ArrayList<>();

        types.addAll(program.types);
        constants.addAll(program.constants);
        functions.addAll(program.functions);
        nodes.addAll(changeMainToTnode(program.nodes, program.main));
        this.types = types;
        this.constants = constants;
        this.functions = functions;
        this.nodes = nodes;

        //generating main node
        assert (this.nodes.get(this.nodes.size() - 1).id.equals(TNODE));
        mainNode = generateMainNode(this.nodes.get(this.nodes.size() - 1), program);

        this.nodes.add(rNode);
        this.nodes.add(rWrapper);
        this.nodes.add(mainNode);
    }


    /**
     * This is used to generate mainNode, that invokes both tNode and rwrapper.
     *
     * @param tNode
     * @return
     */

    public static Node generateMainNode(Node tNode, Program program) {
        List<Expr> wrapperArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(tNode.inputs);
        List<Expr> tNodeArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(tNode.inputs);
        Pair<List<Expr>, List<IdExpr>> wrapperArgsAndRemovedPair = removeOutput(wrapperArgs, InOutManager
                .wrapperOutputNum); //last argument is the
        // output.
        Expr callRwapper = new NodeCallExpr(WRAPPERNODE, wrapperArgsAndRemovedPair.getFirst());

        Equation wrapperCallEq = new Equation(wrapperArgsAndRemovedPair.getSecond(), callRwapper);
        //tNodeArgs.set(tNodeArgs.size() - 1, callRwapper); // settomg the last arguement which is the output, to the
        // output of the wrapper call.
        NodeCallExpr callT = new NodeCallExpr(TNODE, tNodeArgs);
        assert (tNode.outputs.size() == 1); //assuming a single output is possible for TNode to indicate constraints are
        // passing, i.e., sat
        List<VarDecl> mainInList = collectDeclarations((List<IdExpr>) (List<?>) wrapperArgs, tNode, program);

        VarDecl mainOut = new VarDecl("discovery_out", tNode.outputs.get(0).type);
        List mainOutList = new ArrayList();
        mainOutList.add(mainOut);
        Equation mainEq = new Equation(DiscoveryUtil.varDeclToIdExpr(mainOut), callT);
        List mainEquations = new ArrayList();
        mainEquations.add(wrapperCallEq);
        mainEquations.add(mainEq);

        ArrayList<VarDecl> locals = collectDeclarations(wrapperArgsAndRemovedPair.getSecond(), tNode, program);

        return new Node("main", mainInList, mainOutList, locals, mainEquations, null, null, null, null,
                null);

    }

    private static ArrayList<VarDecl> collectDeclarations(List<IdExpr> idExprs, Node tnode, Program program) {
        assert idExprs.size() > 0; //there must be some locals defined in the main to capture the output of the
        // R_wrapper.

        ArrayList<VarDecl> locals = new ArrayList<>();
        for (IdExpr expr : idExprs) {
            locals.add(new VarDecl(expr.id, DiscoveryUtil.lookupExprType(expr, tnode, program)));
        }
        return locals;
    }

    private static Pair<List<Expr>, List<IdExpr>> removeOutput(List<Expr> wrapperArgs, int wrapperOutputNum) {
        int wrapperSize = wrapperArgs.size();
        assert wrapperSize >= wrapperOutputNum; //arguments must be greater than the number of output expected
        // from the wrapper.

        ArrayList<IdExpr> wrapperRemoveOutput = new ArrayList<>();
        for (int i = wrapperSize - wrapperOutputNum; i < wrapperSize; i++) {
            wrapperRemoveOutput.add((IdExpr) wrapperArgs.get(i));
        }

        for (int i = wrapperSize - wrapperOutputNum; i < wrapperSize; i++) {
            wrapperArgs.remove(wrapperArgs.size() - 1);
        }

        return new Pair(wrapperArgs, wrapperRemoveOutput);
    }

    /**
     * This changes the main of the spec to become the T_node.
     *
     * @param nodes
     * @param main
     * @return
     */
    private static List<? extends Node> changeMainToTnode(List<Node> nodes, String main) {
        List<Node> newNodes = new ArrayList<>();
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(main)) {
                Node tnode = generateTnode(nodes.get(i));
                newNodes.addAll(nodes.subList(i + 1, nodes.size())); //adding the rest of the nodes in the tprogram, so that the tnode is always the last node.
                newNodes.add(tnode);
                return newNodes;
            }
            newNodes.add(nodes.get(i));
        }

        System.out.println("cannot find main to convert to T node.");
        assert false;
        return null;
    }

    private static Node generateTnode(Node node) {
        return new Node(TNODE, node.inputs, node.outputs, node.locals, node.equations, node.properties, node
                .assertions, node.realizabilityInputs, node.contract, node.ivc);
    }

    @Override
    public String toString() {

        //return super.toString();
        counterExamplePgm = new Program(Location.NULL, types, constants, functions, nodes, null, "main");

        String programStr = ToLutre.lustreFriendlyString(counterExamplePgm.toString());
        return programStr;

    }

    public Program getCounterExamplePgm() {
        return counterExamplePgm;
    }


    /*
    public static JKindResult search(String fileName, Program pgmT) {
        List<TypeDef> types = new ArrayList<>();
        List<Constant> constants = new ArrayList<>();
        List<Function> functions = new ArrayList<>();
        List<Node> nodes = new ArrayList<>();

        types.addAll(pgmT.types);
        constants.addAll(pgmT.constants);
        functions.addAll(pgmT.functions);
        nodes.addAll(changeMainToTnode(pgmT.nodes, pgmT.main));

        *//* commenting this for now, since our rNode, rWrapper are now static.
        //generating main node
        assert (nodes.get(nodes.size() - 1).id.equals(TNODE));
        Node mainNode = generateMainNode(nodes.get(nodes.size() - 1), pgmT);

        nodes.add(rNode);
        nodes.add(rWrapper);
        nodes.add(mainNode);
*//*

        nodes.add(rNode);
        nodes.add(rWrapper);
        nodes.add(mainNode);

        Program counterExamplePgm = new Program(Location.NULL, types, constants, functions, nodes, "main");

        String programStr = ToLutre.lustreFriendlyString(counterExamplePgm.toString());
        writeToFile(fileName, programStr);
        return DiscoveryUtil.callJkind(fileName, false, -1);
    }
*/

}
