package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class FlattenNodes extends AstMapVisitor {

    //removing that being static
    private int holePostFix = 0;
    private final Program pgm;

    // tights every repair node with the number of copy that have been instantiated for it in the program so far.
    HashMap<String, Integer> repairNodeCopyMap;

    //this contains the newly generated repair nodes that are flattened for the number of calls.
    ArrayList<RepairNode> flattenedRepairNodes = new ArrayList<>();

    // this contains the side effect when visiting repairExpr to collect the new name of the repair node, so when we
    // finish visiting the repairNode we return it with the new name.
    String newRepairNodeName = null;

    public FlattenNodes(Program pgm) {
        repairNodeCopyMap = createRepairNodeMap(pgm);
        this.pgm = pgm;
    }


    @Override
    public Program visit(Program e) {
        List<TypeDef> types = visitTypeDefs(e.types);
        List<Constant> constants = visitConstants(e.constants);
        List<Function> functions = visitFunctions(e.functions);
        List<Node> nodes = visitNodes(e.nodes);
        //List<RepairNode> repairNodes = visitRepairNodes(e.repairNodes);
        return new Program(e.location, types, constants, functions, nodes, flattenedRepairNodes, e.main);
    }


    @Override
    public Expr visit(RepairExpr e) {

        Integer currRepairFlatNum = repairNodeCopyMap.get(e.repairNode.node);
        if(currRepairFlatNum == null){
            System.out.println("repair node does not exist. probably a type error.");
            assert false;
        }



        newRepairNodeName = e.repairNode.node + "_" + (currRepairFlatNum);

        repairNodeCopyMap.put(e.repairNode.node, ++currRepairFlatNum);

        RepairNode repairNode = findRepairNodeDef(e.repairNode.node); //finds the definition of the repair node.

        assert repairNode != null;

        visit(repairNode);  // visits the repairNode to flatten it to the right postfix number and hole unique number
        // . has the side effect of populating the flattenedRepairNodes arraylist.

        RepairExpr flatExpr = new RepairExpr(e.location, e.origExpr, new NodeCallExpr(newRepairNodeName, e.repairNode
                .args));

        newRepairNodeName = null;

        return flatExpr;
    }

    private RepairNode findRepairNodeDef(String node) {
        for (RepairNode nodeDef : pgm.repairNodes) {
            if (nodeDef.id.equals(node))
                return nodeDef;
        }
        return null;
    }


    @Override
    public RepairNode visit(RepairNode e) {
        assert newRepairNodeName != null;

        List<VarDecl> inputs = visitVarDecls(e.inputs);
        List<VarDecl> newHoleinputs = visitUniqueVarDecls(e.holeinputs);

        List<VarDecl> outputs = visitVarDecls(e.outputs);
        List<VarDecl> locals = visitVarDecls(e.locals);

        HashMap<String, Expr> paramToActualBindMap = prepareNodeInput(e.holeinputs, newHoleinputs); // prepares input between
        // old and new holes.

        List<Equation> newEquations = SketchSubsVisitor.execute(e.equations, paramToActualBindMap);
        List<Expr> assertions = visitAssertions(e.assertions);
        Contract contract = visit(e.contract);


        RepairNode flatRepairNode = new RepairNode(e.location, newRepairNodeName, inputs, newHoleinputs, outputs, locals,
                newEquations,
                assertions,
                contract);

        flattenedRepairNodes.add(flatRepairNode);
        return flatRepairNode;
    }

    private HashMap<String, Expr> prepareNodeInput(List<VarDecl> oldHoles, List<VarDecl> newHoles) {

        HashMap<String, Expr> oldHoleNameToNewExpr = new HashMap<>();
        assert oldHoles.size() == newHoles.size(); //otherwise something is wrong.

        for (int i = 0; i < oldHoles.size(); i++)
            oldHoleNameToNewExpr.put(oldHoles.get(i).id, DiscoveryUtil.varDeclToIdExpr(newHoles.get(i)));

        return oldHoleNameToNewExpr;
    }

    //this creates for every hole a new name that is unique.
    private List<VarDecl> visitUniqueVarDecls(List<VarDecl> holeinputs) {
        List<VarDecl> newVarDecl = new ArrayList<>();
        for (VarDecl varDecl : holeinputs) {
            String holeUniqueName = varDecl.id + "_" + holePostFix;
            ++holePostFix;
            newVarDecl.add(new VarDecl(holeUniqueName, varDecl.type));
        }
        return newVarDecl;
    }


    public static Program execute(Program pgm) {
        FlattenNodes flattenNodes = new FlattenNodes(pgm);
        Ast flatPgm = pgm.accept(flattenNodes);
        assert flatPgm instanceof Program;
        return (Program) flatPgm;
    }


    /**
     * Initializes the repair node copy map to contain initially zero for all repair maps,
     *
     * @param pgm
     * @return
     */
    private static HashMap<String, Integer> createRepairNodeMap(Program pgm) {
        HashMap<String, Integer> repairNodeCopyMap = new HashMap<>();

        List<RepairNode> repairNodes = pgm.repairNodes;

        for (RepairNode node : repairNodes)
            repairNodeCopyMap.put(node.id, 0);

        return repairNodeCopyMap;
    }
}
