package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.HashMap;
import java.util.LinkedHashSet;

public class DiscoverContract {
    public static LinkedHashSet<Pair> z3QueryMap = new LinkedHashSet();


    public static Pair<Context, Solver> makeCtxt() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        Solver solver = ctx.mkSolver();
        Pair<Context, Solver> newPair = new Pair<>(ctx, solver);
        z3QueryMap.add(newPair);
        return newPair;
    }

}
