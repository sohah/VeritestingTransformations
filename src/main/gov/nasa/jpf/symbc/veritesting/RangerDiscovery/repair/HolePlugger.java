package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.SynthesisContract;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.Ast;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;
import jkind.results.Signal;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.counterExPropertyName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.loopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.specPropertyName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractMethodName;

public class HolePlugger {
    public final ArrayList<Hole> holes;

    HashMap<Hole, Value> holeSynValuesMap = new HashMap<>();

    JKindResult synReesult;

    Program repairedProgram;

    public HolePlugger(ArrayList<Hole> holes) {
        this.holes = holes;
    }

    public void plugInHoles(JKindResult newResult, Program counterPgm, Program synPgm, NodeRepairKey nodeRepairKey) {
        this.synReesult = newResult;
        populateValuesForHoles();

        repairedProgram = ConstPluggerVisitor.execute(holeSynValuesMap, counterPgm, synPgm, nodeRepairKey);
    }

    private void populateValuesForHoles() {
        for (PropertyResult pr : synReesult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                if (ip.getName().equals(counterExPropertyName)) {
                    Counterexample counterExample = ip.getCounterexample();
                    fillEmptyHoles(counterExample);
                    String fileName = contractMethodName + loopCount + "HoleCEX.lus";

                    DiscoveryUtil.writeToFile(fileName, counterExample.toString());
                }
            }
        }
    }

    private void fillEmptyHoles(Counterexample counterExample) {
        for (int i = 0; i < holes.size(); i++) {
            Hole hole = holes.get(i);
            if (holeSynValuesMap.get(hole) == null) {
                assert (hole instanceof ConstantHole);
                getVarTestValues(counterExample, (ConstantHole) hole);
            }
        }
    }

    private void getVarTestValues(Counterexample counterexample, ConstantHole hole) {
        List<Signal<Value>> signals = counterexample.getSignals();

        for (int i = 0; i < signals.size(); i++) {
            Signal<Value> signal = signals.get(i);
            if (signal.getName().contains(hole.getMyHoleName()))
                if (holeSynValuesMap.get(hole) == null) { //then we need to add it in the map.
                    assert (sameSignalValuesForSteps(signal.getValues()));
                    Value signalValue = signal.getValue(0); // since all values are the same we can get the first one.
                    holeSynValuesMap.put(hole, signalValue);
                    DiscoverContract.holeRepairHolder.updateHoleRepairMap(hole, signalValue);
                }
        }
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

    @Override
    public String toString() {
        return ToLutre.lustreFriendlyString(repairedProgram.toString());
    }
}
