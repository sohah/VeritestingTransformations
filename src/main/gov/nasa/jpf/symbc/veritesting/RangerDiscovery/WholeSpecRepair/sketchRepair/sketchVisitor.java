package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.sketchRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.*;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;
import jkind.lustre.Contract;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;
import jkind.results.Counterexample;
import jkind.results.Signal;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.findNode;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil.findNodeDefByName;

/**
 * This visitor puts back the values of the holes into the specification of T.
 */

public class sketchVisitor extends AstMapVisitor {


    private final Program originalExtnPgm;
    private final Counterexample counterexample;
    private NodeRepairKey nodeRepairKey;

    public sketchVisitor(Program originalExtnPgm, Counterexample counterexample, NodeRepairKey nodeRepairKey) {
        this.originalExtnPgm = originalExtnPgm;
        this.counterexample = counterexample;
        this.nodeRepairKey = nodeRepairKey;
    }


    @Override
    public Node visit(Node e) {
        if (nodeRepairKey.getStatus(e.id) == NodeStatus.REPAIR) {
            List<VarDecl> inputs = visitVarDecls(e.inputs);
            List<VarDecl> outputs = visitVarDecls(e.outputs);
            List<VarDecl> locals = visitVarDecls(e.locals);
            List<Equation> equations = visitEquations(e.equations);
            List<Expr> assertions = visitAssertions(e.assertions);
            List<String> properties = visitProperties(e.properties);
            List<String> ivc = visitIvc(e.ivc);
            List<String> realizabilityInputs = visitRealizabilityInputs(e.realizabilityInputs);
            Contract contract = visit(e.contract);
            return new Node(e.location, e.id, inputs, outputs, locals, equations, properties, assertions,
                    realizabilityInputs, contract, ivc);
        } else return e;
    }


    /**
     * At this point we found an expression to be repaired, thus we need to do the substitution and the partial
     * evaluation.
     */
    @Override
    public Expr visit(RepairExpr e) {
        RepairNode repairNodeDef = DiscoveryUtil.findRepairNodeDef(originalExtnPgm.repairNodes, e.repairNode.node);

        HashMap<Expr, Expr> paramToActualBindMap = prepareNodeInput(e.repairNode, repairNodeDef);


        Ast repairNodeBinded = SketchSubsVisitor.execute(repairNodeDef, paramToActualBindMap);

        Ast partEvalNode = PartialEvalVistor.execute(repairNodeBinded);

        Expr evaluatedExpr = CollapseExprvisitor.execute(partEvalNode);

        return new RepairExpr(e.location, evaluatedExpr, e.repairNode);
    }

    // this method collects the binding for the input of the repair nodes.
    private HashMap<Expr,Expr> prepareNodeInput(NodeCallExpr repairNodeCall, RepairNode repairNodeDef) {
        HashMap<Expr, Expr> paramToInputMap = new LinkedHashMap<>();

        assert(repairNodeCall.args.size() == repairNodeDef.inputs.size());

        //this fills in the binding: formal binding -> actual binding
        for(int i=0; i<repairNodeCall.args.size(); i++){
            paramToInputMap.put(DiscoveryUtil.varDeclToIdExpr(repairNodeDef.inputs.get(i)), repairNodeCall.args.get(i));
        }

        //this adds the binding for the holes using the counter example generated.
        for(VarDecl holeVarDecl: repairNodeDef.holeinputs){
            paramToInputMap.put(DiscoveryUtil.varDeclToIdExpr(holeVarDecl), getVarTestValues(holeVarDecl));
        }

        return paramToInputMap;
    }


    private Expr getVarTestValues(VarDecl holeVarDecl) {
        List<Signal<Value>> signals = counterexample.getSignals();

        for (int i = 0; i < signals.size(); i++) {
            Signal<Value> signal = signals.get(i);
            if (signal.getName().contains(holeVarDecl.id)) {
                assert (sameSignalValuesForSteps(signal.getValues()));
                Value signalValue = signal.getValue(0); // since all values are the same we can get the first one.
                return DiscoveryUtil.valueToExpr(signalValue, holeVarDecl.type);
            }
        }
        return null;
    }


    private boolean sameSignalValuesForSteps(Map<Integer, Value> values) {
        assert (values.size() != 0);
        Value initialValue = values.get(0);

        for (Map.Entry entry : values.entrySet()) { //we will do one extra initial check.
            if (!initialValue.equals(entry.getValue()))
                return false;
        }
        return true;
    }


    public static Program execute(Program counterExamplePgm, Program synthesisPgm, NodeRepairKey nodeRepairKey) {


        List<Node> toRepairNodes = getToRepairNodes(counterExamplePgm, nodeRepairKey);
        List<Node> repairedNodes = new ArrayList<>();

        sketchVisitor constPluggerVisitor = new sketchVisitor(counterExamplePgm, synthesisPgm);

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
}
