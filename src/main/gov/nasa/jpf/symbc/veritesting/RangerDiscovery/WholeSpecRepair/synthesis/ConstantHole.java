package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.WholeSpecRepair.synthesis;

import jkind.lustre.IdExpr;
import jkind.lustre.Location;

import java.util.Objects;

public class ConstantHole extends IdExpr implements Hole , Cloneable{
    private static int prefix = 0;
    private static String holeName = "hole";
    public final int myPrefix;

    public ConstantHole(Location location, String id) {
        super(location, (holeName + "_" + prefix));
        myPrefix = prefix;
        prefix++;
    }

    public ConstantHole(String id) {
        super(holeName + "_" + prefix);
        myPrefix = prefix;
        prefix++;
    }

    public static int getCurrentHolePrefix(){
        return prefix;
    }

    public static String recreateHoleName(int id){
        return holeName + "_" + id;
    }

    public String getMyHoleName(){
        return holeName + "_" + myPrefix;
    }

    @Override
    public boolean isEqual(Hole anotherHole) {
        return (this.getMyHoleName().equals(((ConstantHole)anotherHole).getMyHoleName()));
    }

    @Override
    public int hashCode(){
        return Objects.hashCode(myPrefix);
    }
}
