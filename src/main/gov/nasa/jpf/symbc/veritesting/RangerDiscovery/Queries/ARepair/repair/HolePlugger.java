package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.repair;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.LustreTranslation.ToLutre;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.NodeRepairKey;
import jkind.api.results.JKindResult;
import jkind.lustre.Program;

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
