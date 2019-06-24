package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.repair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.ConstantHole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.HoleRepairState;
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

    JKindResult synReesult;

    Program repairedProgram;

    public void plugInHoles(JKindResult synReesult, Program counterPgm, Program synPgm, NodeRepairKey nodeRepairKey) {
        this.synReesult = synReesult;
        repairedProgram = ConstPluggerVisitor.execute(counterPgm, synPgm, nodeRepairKey);
    }

    @Override
    public String toString() {
        return ToLutre.lustreFriendlyString(repairedProgram.toString());
    }
}
