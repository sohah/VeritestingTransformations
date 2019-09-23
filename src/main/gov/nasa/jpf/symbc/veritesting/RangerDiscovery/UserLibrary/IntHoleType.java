package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.UserLibrary;


import jkind.lustre.Location;
import jkind.lustre.Type;


public class IntHoleType extends HoleType {
	public final String id  = "intHole";

	public IntHoleType(Location location) {
		super(location);
	}

	@Override
	public <T> T accept(jkind.lustre.visitors.TypeVisitor<T> visitor) {
		return null;
	}

	public IntHoleType() {
		this(Location.NULL);
	}

	@Override
	public String toString() {
		return id;
	}

	@Override
	public int hashCode() {
		return id.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof IntHoleType) {
			IntHoleType et = (IntHoleType) obj;
			return id.equals(et.id);
		}
		return false;
	}

	public <T> T accept(TypeVisitor<T> visitor) {
		return visitor.visit(this);
	}
}