package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.*;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;
import jkind.results.Signal;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.counterExPropertyName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.loopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractMethodName;

/**
 * maintains the last value of repair for each hole.
 */
public class HoleRepairState {

    // for every hole, the map maintains the initial value that was used in the spec
    private HashMap<Hole, Ast> holeIntialValueMap = new HashMap<>();

    //for every hole, all repaired values attached to it, where the last value is the last repair found.
    private HashMap<Hole, List<Ast>> holeRepairValuesMap = new HashMap();

    private HashMap<Hole, Type> holeTypeMap = new HashMap<>();


    public void createNewHole(Hole hole, Ast initialValue, Type type) {
        assert Config.loopCount == 0; // creating holes should only happen in the initial step
        holeIntialValueMap.put(hole, initialValue);
        holeTypeMap.put(hole, type);
    }

    /*private HashMap<Hole, Type> collectHoleType(Node main) {
        HashMap<Hole, Type> myHoleTypeMap = new HashMap<>();

        List<VarDecl> inputList = main.inputs;
        List<Hole> holesList = (List<Hole>) holeRepairValuesMap.keySet();
        for (int i = 0; i < holesList.size() - 1; i++) {
            for (int j = 0; j < inputList.size() - 1; i++) {
                if (holesList.get(i).toString().equals(inputList.toString())) //same hole name
                    myHoleTypeMap.put(holesList.get(i), inputList.get(j).type);
            }
        }
        return myHoleTypeMap;
    }
*/

    public void plugInHoles(JKindResult synResult, Program counterPgm, Program synPgm, NodeRepairKey nodeRepairKey) {
        for (PropertyResult pr : synResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                if (ip.getName().equals(counterExPropertyName)) {
                    Counterexample counterExample = ip.getCounterexample();
                    fillHolesWithRepairs(counterExample);
                    String fileName = contractMethodName + loopCount + "HoleCEX.txt";
                    DiscoveryUtil.writeToFile(fileName, counterExample.toString());
                }
            }
        }

    }

    private void fillHolesWithRepairs(Counterexample counterExample) {

        for (Map.Entry entry : holeRepairValuesMap.entrySet()) {
            Hole hole = (Hole) entry.getKey();
            assert hole instanceof ConstantHole; // currently only supporting constants
            Ast repairValue = getVarTestValues(counterExample, (ConstantHole) hole);
            if (repairValue != null)
                updateRepairValue(hole, repairValue);
        }
    }

    private Ast getVarTestValues(Counterexample counterexample, ConstantHole hole) {
        List<Signal<Value>> signals = counterexample.getSignals();

        for (int i = 0; i < signals.size(); i++) {
            Signal<Value> signal = signals.get(i);
            if (signal.getName().contains(hole.getMyHoleName()))
                assert (sameSignalValuesForSteps(signal.getValues()));
            Value signalValue = signal.getValue(0); // since all values are the same we can get the first one.
            return DiscoveryUtil.valueToExpr(signalValue, holeTypeMap.get(hole));
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

    //filles the holeRepairValuesMap with only the keys filled in.
    public void createEmptyHoleRepairValues() {
        for (Map.Entry entry : holeIntialValueMap.entrySet()) {
            holeRepairValuesMap.put((Hole) entry.getKey(), new ArrayList<>());
        }
    }


    //gets the last repair value otherwise returns the initial value of the object as the value of the last repair,
    // thus the value of the last repair needs to be updated to the initial value being returned.
    public Ast getLastRepairOrInitial(Hole hole) {
        Ast repairValue = DiscoveryUtil.getLastElementInMap(holeRepairValuesMap, hole);
        if (repairValue == null) { // no repair yet for the hole
            Ast initialValue = holeIntialValueMap.get(hole);
            updateRepairValue(hole, initialValue);
            assert initialValue != null;
            return initialValue;
        } else
            return repairValue;
    }

    //updates the repair value for a hole.
    public void updateRepairValue(Hole hole, Ast newRepair) {
        List<Ast> repairValues = holeRepairValuesMap.get(hole);
        repairValues.add(newRepair);
        return;
    }

    //returns the last repair value for a hole if it exists, otherwise assume default value
    public Ast getLastRepairOrDefaultValue(Hole hole) {
        Ast repairValue = DiscoveryUtil.getLastElementInMap(holeRepairValuesMap, hole);
        if (repairValue == null) { // no repair yet for the hole
            Type type = holeTypeMap.get(hole);
            if (type == NamedType.BOOL) {
                repairValue = Config.defaultHoleValBool;
                updateRepairValue(hole, repairValue);
                return repairValue;
            } else if (type == NamedType.INT) {
                repairValue = Config.defaultHoleValInt;
                updateRepairValue(hole, repairValue);
                return repairValue;
            } else {
                System.out.println("unsupported hole type!");
                assert false;
                return null;
            }
        } else return repairValue;

    }


    //prints repaired values for the hole
    public String toString() {
        String mapStr = "";
        for (HashMap.Entry entry : holeRepairValuesMap.entrySet()) {
            Ast value = (Ast) entry.getValue();
            Ast initialValue = holeIntialValueMap.get(entry.getKey());
            mapStr += entry.getKey().toString() + " -> (" + initialValue + value + ")\n";
        }
        return mapStr;
    }
}
