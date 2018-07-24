package gov.nasa.jpf.symbc.veritesting.ast.transformations;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;

import java.util.HashSet;
import java.util.Set;

/* Data class defining interface for transformations.

 */

public class TransformationData {
    public final Region region;
    public final Set<Invariant> invariants;
    public final boolean runInvariants;

    public TransformationData(Region region, Set<Invariant> invariants, boolean runInvariants) {
        this.region = region;
        this.invariants = invariants;
        this.runInvariants = runInvariants;
    }

    public void checkInvariants() throws StaticRegionException {
        if (runInvariants) {
            for (Invariant i: invariants) {
                i.checkInvariant(region);
            }
        }
    }
}
