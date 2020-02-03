package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreExtension;


/**
 * The purpose of this visitor is:
 * 1. create a new program with the right input of holes collected from visiting repaired nodes.
 * 2. populating the RepairNode
 */

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ConstantHoleExtn;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import jkind.lustre.*;
import jkind.lustre.visitors.AstMapVisitor;

import java.util.*;

public class LustreAstMapExtnVisitor extends AstMapVisitor {
    public static HashMap<String, List<VarDecl>> nodeToHoleVarDeclMap = new HashMap<String, List<VarDecl>>();
    List<Node> newNodes = new ArrayList<>();
    public static List<RepairNode> existingRepairNodes = new ArrayList<>();

    public static void resetState(){
        nodeToHoleVarDeclMap = new HashMap<>();
    }

    @Override
    public Constant visit(Constant e) {
        return new Constant(e.location, e.id, e.type, e.expr.accept(this));
    }

    @Override
    public Equation visit(Equation e) {
        // Do not traverse e.lhs since they do not really act like Exprs
        return new Equation(e.location, e.lhs, e.expr.accept(this));
    }

    @Override
    public Function visit(Function e) {
        List<VarDecl> inputs = visitVarDecls(e.inputs);
        List<VarDecl> outputs = visitVarDecls(e.outputs);
        return new Function(e.location, e.id, inputs, outputs);
    }

    @Override
    public Node visit(Node e) {
        List<VarDecl> inputs = visitVarDecls(e.inputs);
        List<VarDecl> outputs = visitVarDecls(e.outputs);
        List<VarDecl> locals = visitVarDecls(e.locals);
        List<Equation> equations = visitEquations(e.equations);
        List<Expr> assertions = visitAssertions(e.assertions);
        List<String> properties = visitProperties(e.properties);
        List<String> ivc = visitIvc(e.ivc);
        List<String> realizabilityInputs = visitRealizabilityInputs(e.realizabilityInputs);
        Contract contract = visit(e.contract);

        if (e.id.equals("main")) {//for all the hole inputs that we have discovered add them to main.
            for (Map.Entry<String, List<VarDecl>> entry : nodeToHoleVarDeclMap.entrySet()) {
                inputs.addAll(entry.getValue());
            }
        }
        return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                realizabilityInputs, contract, ivc);
    }

    //changes are happening here

    @Override
    public RepairNode visit(RepairNode e) {
        existingRepairNodes.add(e);
        List<VarDecl> inputs = visitVarDecls(e.inputs);
        List<VarDecl> holeinputs = visitVarDecls(e.holeinputs);
        nodeToHoleVarDeclMap.put(e.id, holeinputs);
        inputs.addAll(holeinputs);

        List<VarDecl> outputs = visitVarDecls(e.outputs);
        List<VarDecl> locals = visitVarDecls(e.locals);
        List<Equation> equations = visitEquations(e.equations);
        List<Expr> assertions = visitAssertions(e.assertions);
        Contract contract = visit(e.contract);
        newNodes.add(new Node(e.location, e.id, inputs, outputs, locals, equations, null, assertions,
                null, contract, null));

        return new RepairNode(e.location, e.id, inputs, null, outputs, locals, equations, assertions, contract);
    }


    protected List<VarDecl> visitVarDecls(List<VarDecl> es) {
        return map(this::visit, es);
    }

    protected List<Equation> visitEquations(List<Equation> es) {
        return map(this::visit, es);
    }

    protected List<Expr> visitAssertions(List<Expr> es) {
        return visitExprs(es);
    }

    protected List<String> visitProperties(List<String> es) {
        return map(this::visitProperty, es);
    }

    protected String visitProperty(String e) {
        return e;
    }

    protected List<String> visitIvc(List<String> es) {
        return map(this::visitIvc, es);
    }

    protected String visitIvc(String e) {
        return e;
    }

    protected List<String> visitRealizabilityInputs(List<String> es) {
        if (es == null) {
            return null;
        }
        return map(this::visitRealizabilityInput, es);
    }

    protected String visitRealizabilityInput(String e) {
        return e;
    }

    //changes are happening here
    @Override
    public Program visit(Program e) {
        List<TypeDef> types = visitTypeDefs(e.types);
        List<Constant> constants = visitConstants(e.constants);
        List<Function> functions = visitFunctions(e.functions);

        List<RepairNode> repairNodes = visitRepairNodes(e.repairNodes); //repair nodes are ignored, and their side
        List<Node> nodes = visitNodes(e.nodes);

        // effect of creating new normal nodes are collected in newNodes.
        nodes.addAll(newNodes); //collecting from the side effect, since the visitor must return something of the
        // same type.
        return new Program(e.location, types, constants, functions, nodes, null, e.main);
    }

    protected List<TypeDef> visitTypeDefs(List<TypeDef> es) {
        return map(this::visit, es);
    }

    protected List<Constant> visitConstants(List<Constant> es) {
        return map(this::visit, es);
    }

    protected List<Node> visitNodes(List<Node> es) {
        return map(this::visit, es);
    }


    //changes are happening here.
    protected List<RepairNode> visitRepairNodes(List<RepairNode> es) {
        for (RepairNode repairNode : es) {
            visit(repairNode);
        }
        return es;
    }

    protected List<Function> visitFunctions(List<Function> es) {
        return map(this::visit, es);
    }

    @Override
    public TypeDef visit(TypeDef e) {
        return e;
    }


    //changes are happening here.
    @Override
    public VarDecl visit(VarDecl e) {
        if (e.type.toString().equals("boolhole"))
            return new VarDecl(e.id, NamedType.BOOL);
        else if (e.type.toString().equals("inthole"))
            return new VarDecl(e.id, NamedType.INT);
        else
            return e;
    }

    @Override
    public Contract visit(Contract contract) {
        if (contract == null) {
            return null;
        }
        return new Contract(visitExprs(contract.requires), visitExprs(contract.ensures));
    }


    //changes are happening here.
    @Override
    public Expr visit(RepairExpr e) {
        NodeCallExpr nodeCallExpr = e.repairNode;

        List<VarDecl> inputVarDecls = nodeToHoleVarDeclMap.get(nodeCallExpr.node);

        List<IdExpr> inputExpr = DiscoveryUtil.varDeclToIdExpr(inputVarDecls);
        List<Expr> holeVars = (List<Expr>) (List<? extends Expr>) inputExpr;
        List<Expr> args = new ArrayList<>(nodeCallExpr.args);
        args.addAll(holeVars);

        return new NodeCallExpr(nodeCallExpr.node, args);
    }

    public static Program execute(Program origLustreExtPgm) {
        Ast newProgram = origLustreExtPgm.accept(new LustreAstMapExtnVisitor());
        assert (newProgram instanceof Program);
        return (Program) newProgram;
    }

    public static ArrayList<Hole> getHoles() {
        ArrayList<Hole> holes = new ArrayList<>();

        Iterator<Map.Entry<String, List<VarDecl>>> mapItr = nodeToHoleVarDeclMap.entrySet().iterator();

        while (mapItr.hasNext()) {
            Map.Entry<String, List<VarDecl>> nodeVarDecls = mapItr.next();
            for (VarDecl var : nodeVarDecls.getValue()) {
                ConstantHoleExtn holeExtn = new ConstantHoleExtn(var.id, NamedType.get(var.type.toString()));
                if (holes.contains(holeExtn)) {
                    System.out.println("duplicate expression Ids are found for holes with library extension, the assumption is that the holes are uniquely defined by the user among all the nodes! Aborting");
                    assert false;
                }
                holes.add(holeExtn);
            }
        }
        return holes;
    }
}
