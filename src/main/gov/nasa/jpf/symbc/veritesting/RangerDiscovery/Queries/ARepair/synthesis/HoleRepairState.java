package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util.DiscoveryUtil;
import jkind.api.results.JKindResult;
import jkind.api.results.PropertyResult;
import jkind.lustre.*;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;
import jkind.results.Signal;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.counterExPropertyName;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.currFaultySpec;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.loopCount;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.permutationCount;

/**
 * This is the main class that maintains the holes we want to repair. Initially it is populated with the holes and
 * their initial values and the type for each hole. In every iteration, one entry in the list of its
 * holeRepairValuesMap gets added to indicate the next repair.
 * The repaired values is first selected from the counter example, if not found then selected from the last repair,
 * if there was any, if not found then it is selected from either some default value that the tool sets in the Config
 * or it is set to the initial value associated with the hole in the original spec. This is also setup in the Config
 * option useInitialSpecValues.
 */
public class HoleRepairState {

    // for every hole, the map maintains the initial value that was used in the spec
    private HashMap<Hole, Ast> holeIntialValueMap = new HashMap<>();

    //for every hole, all repaired values attached to it, where the last value is the last repair found.
    private HashMap<Hole, List<Ast>> holeRepairValuesMap = new HashMap();

    private HashMap<Hole, Type> holeTypeMap = new HashMap<>();


    public void createNewHole(Hole hole, Ast initialValue, Type type) {
        assert loopCount == 0; // creating holes should only happen in the initial step
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

    public void plugInHoles(JKindResult synResult) {
        for (PropertyResult pr : synResult.getPropertyResults()) {
            if (pr.getProperty() instanceof InvalidProperty) {
                InvalidProperty ip = (InvalidProperty) pr.getProperty();
                if (ip.getName().equals(counterExPropertyName)) {
                    Counterexample counterExample = ip.getCounterexample();
                    fillHolesWithRepairs(counterExample);
                    String fileName;
                    if (Config.specLevelRepair)
                        fileName = currFaultySpec + "_" + loopCount + "_" + "holeCEX.txt";
                    else
                        fileName = "def_" + currFaultySpec + "_" + permutationCount + "_" + loopCount + "_" + "holeCEX.txt";
                    DiscoveryUtil.writeToFile(fileName, counterExample.toString(),false);
                }
            }
        }

    }

    private void fillHolesWithRepairs(Counterexample counterExample) {

        for (Map.Entry entry : holeRepairValuesMap.entrySet()) {
            Hole hole = (Hole) entry.getKey();
            Ast repairValue = null;
            if (hole instanceof ConstantHole) {
                repairValue = getVarTestValues(counterExample, (ConstantHole) hole);
                if (repairValue == null)
                    if (Config.useInitialSpecValues) {
                        repairValue = getLastRepairOrInitial(hole);
                    } else {
                        repairValue = getLastRepairOrDefaultValue(hole);
                    }
            } else if (hole instanceof PreHoleContainer) {
                repairValue = getVarTestValues(counterExample, (PreHoleContainer) hole);
                if (repairValue == null)
                    if (Config.useInitialSpecValues) {
                        repairValue = getLastRepairOrInitial(hole);
                    } else {
                        repairValue = getLastRepairOrDefaultValue(hole);
                    }
            } else
                assert false; //no other types of repairs are defined yet.
            updateRepairValue(hole, repairValue);
        }
    }

    private Ast getVarTestValues(Counterexample counterexample, ConstantHole hole) {
        List<Signal<Value>> signals = counterexample.getSignals();

        for (int i = 0; i < signals.size(); i++) {
            Signal<Value> signal = signals.get(i);
            if (signal.getName().contains(hole.getMyHoleName())) {
                assert (sameSignalValuesForSteps(signal.getValues()));
                Value signalValue = signal.getValue(0); // since all values are the same we can get the first one.
                return DiscoveryUtil.valueToExpr(signalValue, holeTypeMap.get(hole));
            }
        }
        return null;
    }


    private Ast getVarTestValues(Counterexample counterexample, PreHoleContainer holeContainer) {
        List<Signal<Value>> signals = counterexample.getSignals();

        for (int i = 0; i < signals.size(); i++) {
            Signal<Value> signal = signals.get(i);
            if (signal.getName().contains(holeContainer.getContainerName())) {

                ConstantHole conditionHole = (ConstantHole) holeContainer.myHoles.get(0);

                Integer signalIndex = findSignalIndex(signals, conditionHole.getMyHoleName());
                Signal<Value> conditionSignal = signals.get(signalIndex);

                assert (sameSignalValuesForSteps(conditionSignal.getValues()));

                Value conditionSignalValue = conditionSignal.getValue(0); // since all values are the same we can get the
                // first
                // one.
                assert (conditionSignalValue instanceof BooleanValue);
                if (((BooleanValue) conditionSignalValue).value)
                    return getRepairedPreContainerExpr(holeContainer.thenExpr, signals); // indicating the thenExpr
                else
                    return getRepairedPreContainerExpr(holeContainer.elseExpr, signals); // indicating the elseExpr
            }
        }
        return null;
    }

    /**
     * this tries to rebuild the expression of repair
     *
     * @param expr
     * @param signals
     * @return
     */
    private Ast getRepairedPreContainerExpr(Expr expr, List<Signal<Value>> signals) {
        if ((expr instanceof IdExpr) || ((expr instanceof UnaryExpr) && (((UnaryExpr) expr).op == UnaryOp.PRE)))
            return expr;
        else if ((expr instanceof BinaryExpr) && (((BinaryExpr) expr).op == BinaryOp.ARROW)) { // then the left
            // handside of the arrow must be a hole that represents the init value
            assert (((BinaryExpr) expr).left instanceof ConstantHole);
            ConstantHole initHole = (ConstantHole) ((BinaryExpr) expr).left;
            Integer index = findSignalIndex(signals, initHole.getMyHoleName());

            if (index != null) {
                Signal<Value> initSignal = signals.get(index);
                assert (sameSignalValuesForSteps(initSignal.getValues()));
                Value signalValue = initSignal.getValue(0); // since all values are the same we can get the first one.
                Expr initHoleRepairExpr = DiscoveryUtil.valueToExpr(signalValue, holeTypeMap.get(initHole));
                return new BinaryExpr(initHoleRepairExpr, BinaryOp.ARROW, ((BinaryExpr) expr).right);
            }
        } else // we are not expecting other forms for preExpressions
            assert false;
        return null;
    }


    private Integer findSignalIndex(List<Signal<Value>> signals, String name) {
        int i = 0;
        while (i < signals.size()) {
            Signal<Value> signal = signals.get(i);
            if (signal.getName().contains(name))
                return i;
            i++;
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

    public Ast getRepairValue(Hole hole) {
        List<Ast> repairs = holeRepairValuesMap.get(hole);
        return repairs.get(repairs.size() - 1);
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
            List<Ast> valueList = (List<Ast>) entry.getValue();
            Ast initialValue = holeIntialValueMap.get(entry.getKey());
            mapStr += entry.getKey().toString() + " -> (" + initialValue + "," + valueList + ")\n";
        }
        return mapStr;
    }
}
