package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis;

import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;

import java.util.Objects;

public class ConstantHoleExtn extends IdExpr implements Hole, Cloneable {
    public final NamedType myType;

    public ConstantHoleExtn(String id, NamedType type) {
        super(id);
        myType = type;
    }

    @Override
    public boolean isEqual(Hole anotherHole) {
        return (this.id.equals(((ConstantHoleExtn) anotherHole).id) && (this.myType.equals(((ConstantHoleExtn) anotherHole).myType)));
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(id);
    }

}
