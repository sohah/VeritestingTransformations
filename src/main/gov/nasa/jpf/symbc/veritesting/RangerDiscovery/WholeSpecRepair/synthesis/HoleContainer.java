package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import jkind.lustre.*;

import java.util.ArrayList;
import java.util.Objects;

public class HoleContainer extends IdExpr implements Hole, Cloneable {
    private static int prefix = 0;
    private static String containerName = "container";

    public final int myPrefix;
    public final NamedType myType;


    //this is used to hold possible values
    ArrayList<Hole> myHoles = new ArrayList<>();

    public HoleContainer(String id, NamedType containerType, ArrayList<Hole> holes) {
        super(containerName + "_" + prefix);
        myPrefix = prefix;
        myType = containerType;
        myHoles = holes;
        prefix++;
    }

    /*public static int getCurrentHolePrefix() {
        return prefix;
    }
*/
    /*public static String recreateHoleName(int id) {
        return containerName + "_" + id;
    }*/

    public String getContainerName() {
        return containerName + "_" + myPrefix;
    }

    @Override
    public boolean isEqual(Hole holeContainer) {
        assert (holeContainer instanceof  HoleContainer);

        return (this.getContainerName().equals(((HoleContainer) holeContainer).getContainerName()));
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(getContainerName());
    }

}
