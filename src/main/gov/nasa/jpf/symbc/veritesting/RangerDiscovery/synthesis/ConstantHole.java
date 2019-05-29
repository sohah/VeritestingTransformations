package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import jkind.lustre.IdExpr;
import jkind.lustre.Location;

public class ConstantHole extends IdExpr implements Hole {
    private static int prefix = 0;
    private static String holeName = "hole";

    public ConstantHole(Location location, String id) {
        super(location, (holeName + "_" + prefix));
        prefix++;
    }

    public ConstantHole(String id) {
        super(holeName + "_" + prefix);
        prefix++;
    }
}
