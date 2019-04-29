package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.sketchRepair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.*;
import jkind.lustre.Contract;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.AstMapVisitor;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;
import jkind.results.Signal;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.counterExPropertyName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.currFaultySpec;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.loopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair.MinimalRepairDriver.candidateLoopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.MinimalRepair.MinimalRepairDriver.knownRepairLoopCount;

/**
 * This visitor puts back the values of the holes into the specification of T.
 */

public class SketchVisitor extends AstMapVisitor {


    private final Program originalExtnPgm;
    private final Counterexample counterexample;

    public SketchVisitor(Program originalExtnPgm, Counterexample counterexample) {
        this.originalExtnPgm = originalExtnPgm;
        this.counterexample = counterexample;
    }


    @Override
    public Node visit(Node e) {
        if (e.id.equals("main")) { //repairing main node
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

        HashMap<String, Expr> paramToActualBindMap = prepareNodeInput(e.repairNode, repairNodeDef);


        Ast repairNodeBinded = SketchSubsVisitor.execute(repairNodeDef, paramToActualBindMap);

        Ast partEvalNode = PartialEvalVisitor.execute(repairNodeBinded);

        Expr evaluatedExpr = CollapseExprVisitor.execute(partEvalNode, new HashSet<>(paramToActualBindMap.values()));

        return new RepairExpr(e.location, evaluatedExpr, e.repairNode);
    }

    // this method collects the binding for the input of the repair nodes.
    private HashMap<String, Expr> prepareNodeInput(NodeCallExpr repairNodeCall, RepairNode repairNodeDef) {
        HashMap<String, Expr> paramToInputMap = new LinkedHashMap<>();

        assert (repairNodeCall.args.size() == repairNodeDef.inputs.size());

        //this fills in the binding: formal binding -> actual binding
        for (int i = 0; i < repairNodeCall.args.size(); i++) {
            paramToInputMap.put(DiscoveryUtil.varDeclToIdExpr(repairNodeDef.inputs.get(i)).id, repairNodeCall.args.get
                    (i));
        }

        //this adds the binding for the holes using the counter example generated.
        for (VarDecl holeVarDecl : repairNodeDef.holeinputs) {
            paramToInputMap.put(DiscoveryUtil.varDeclToIdExpr(holeVarDecl).id, getVarTestValues(holeVarDecl));
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


    public static Program execute(Program originalExtPgm, JKindResult synResult, boolean isMinimal) {

        Counterexample counterExample = null;
        for (PropertyResult pr : synResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                if (ip.getName().equals(counterExPropertyName)) {
                    counterExample = ip.getCounterexample();
                }
            }
        }

        assert (counterExample != null);

        //logging
        String fileName;
        if (isMinimal)
            fileName = currFaultySpec + "_" + knownRepairLoopCount+ "_" + candidateLoopCount + "_" + "holeCEX.txt";
        else
            fileName = currFaultySpec + "_" + loopCount + "_" + "holeCEX.txt";

        DiscoveryUtil.writeToFile(fileName, counterExample.toString(), isMinimal);

        SketchVisitor sketchVisitor = new SketchVisitor(originalExtPgm, counterExample);

        Ast newProgram = originalExtPgm.accept(sketchVisitor);
        assert newProgram instanceof Program;

        return (Program) newProgram;
    }
}
