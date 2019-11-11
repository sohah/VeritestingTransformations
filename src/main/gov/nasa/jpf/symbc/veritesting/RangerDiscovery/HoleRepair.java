package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.Ast;
import jkind.lustre.values.Value;

import java.util.HashMap;

public class HoleRepair {

    public HashMap<Hole, Pair<Ast, Value>> holeRepairMap;

    public void setHoleRepairMap(HashMap<Hole, Pair<Ast, Value>> holeRepairMap) {
        this.holeRepairMap = holeRepairMap;
    }

    public String toString() {
        String mapStr ="";
        for (HashMap.Entry entry : holeRepairMap.entrySet()) {
            Pair<Ast, Value> value = (Pair<Ast, Value>) entry.getValue();
            mapStr += entry.getKey().toString() + " -> (" + value.getFirst() +"," + value.getSecond()+")\n";
        }
        return mapStr;
    }

    public void updateHoleRepairMap(ConstantHole hole, Value signalValue) {
        Pair<Ast, Value> holeValue = this.holeRepairMap.get(hole);
        holeValue.putSecond(signalValue);
    }
}
