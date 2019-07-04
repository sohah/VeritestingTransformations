package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.counterExample;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import jkind.api.results.JKindResult;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.TNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.WRAPPERNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.writeToFile;


/**
 * This class holds the T program, that can be used for either the counter Example step or the synthesis step.
 */
public class CounterExContract {
    public final List<TypeDef> types;
    public final List<Constant> constants;
    public final List<Function> functions;
    public final List<Node> nodes;

    public final Node rNode;
    public final Node rWrapper;
    public final Node mainNode;

    private Program counterExamplePgm;

    /**
     * Generates a T program counter example step from a file path, usually this is done in the first time.
     *
     * @return
     */
    public CounterExContract(DynamicRegion dynRegion, Program program, Contract contract) {

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
        mainNode = generateMainNode(this.nodes.get(this.nodes.size() - 1));

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

    public static Node generateMainNode(Node tNode) {
        List<Expr> wrapperArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(tNode.inputs);
        List<Expr> tNodeArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(tNode.inputs);
        wrapperArgs.remove(wrapperArgs.size() - 1); //last argument is the output.
        Expr callRwapper = new NodeCallExpr(WRAPPERNODE, wrapperArgs);
        tNodeArgs.set(tNodeArgs.size() - 1, callRwapper); // settomg the last arguement which is the output, to the output of the wrapper call.
        NodeCallExpr callT = new NodeCallExpr(TNODE, (List<Expr>) tNodeArgs);
        assert (tNode.outputs.size() == 1); //assuming a single output is possible for TNode to indicate constraints are
        // passing, i.e., sat
        List mainInList = new ArrayList();
        mainInList.addAll(tNode.inputs);
        mainInList.remove(mainInList.size()-1); //removing the last element because that is an output

        VarDecl mainOut = new VarDecl("discovery_out", tNode.outputs.get(0).type);
        List mainOutList = new ArrayList();
        mainOutList.add(mainOut);
        Equation mainEq = new Equation(DiscoveryUtil.varDeclToIdExpr(mainOut), callT);
        List mainEquations = new ArrayList();
        mainEquations.add(mainEq);

        return new Node("main", mainInList, mainOutList, null, mainEquations, null, null, null, null,
                null);

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
        counterExamplePgm = new Program(Location.NULL, types, constants, functions, nodes, "main");

        String programStr = ToLutre.lustreFriendlyString(counterExamplePgm.toString());
        return programStr;

    }

    public Program getCounterExamplePgm() {
        return counterExamplePgm;
    }


    public static JKindResult search(String fileName, Program pgmT, Node rNode, Node rWrapper) {
        List<TypeDef> types = new ArrayList<>();
        List<Constant> constants = new ArrayList<>();
        List<Function> functions = new ArrayList<>();
        List<Node> nodes = new ArrayList<>();

        types.addAll(pgmT.types);
        constants.addAll(pgmT.constants);
        functions.addAll(pgmT.functions);
        nodes.addAll(changeMainToTnode(pgmT.nodes, pgmT.main));

        //generating main node
        assert (nodes.get(nodes.size() - 1).id.equals(TNODE));
        Node mainNode = generateMainNode(nodes.get(nodes.size() - 1));

        nodes.add(rNode);
        nodes.add(rWrapper);
        nodes.add(mainNode);

        Program counterExamplePgm = new Program(Location.NULL, types, constants, functions, nodes, "main");

        String programStr = ToLutre.lustreFriendlyString(counterExamplePgm.toString());
        writeToFile(fileName, programStr);
        return DiscoveryUtil.callJkind(fileName, false, -1);
    }


}
