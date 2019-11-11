package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

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

    public String getContainerName() {
        return containerName + "_" + myPrefix;
    }

    @Override
    public boolean isEqual(Hole holeContainer) {
        assert (holeContainer instanceof HoleContainer);

        return (this.getContainerName().equals(((HoleContainer) holeContainer).getContainerName()));
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(getContainerName());
    }

    public Expr getContainerFreezeAssertion() {
        return new jkind.lustre.BinaryExpr(new BoolExpr(true), BinaryOp.ARROW, (new jkind.lustre.BinaryExpr(new IdExpr
                (getContainerName()), BinaryOp.EQUAL, new
                UnaryExpr(UnaryOp.PRE, new IdExpr(getContainerName())))));
    }

}
