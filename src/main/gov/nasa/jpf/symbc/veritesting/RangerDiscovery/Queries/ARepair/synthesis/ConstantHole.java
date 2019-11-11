package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;

import java.util.Objects;

public class ConstantHole extends IdExpr implements Hole , Cloneable{
    private static int prefix = 0;
    private static String holeName = "hole";
    public final int myPrefix;
    public final NamedType myType;

    public ConstantHole(String id, NamedType type) {
        super(holeName + "_" + prefix);
        myPrefix = prefix;
        myType = type;
        prefix++;
    }

    public static void resetCount(){
        prefix = 0;
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
