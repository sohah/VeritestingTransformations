package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.UserLibrary;


import jkind.lustre.Location;


public class BoolHoleType extends HoleType {
	public final String id  = "BoolHole";

	public BoolHoleType(Location location) {
		super(location);
	}

	@Override
	public <T> T accept(jkind.lustre.visitors.TypeVisitor<T> visitor) {
		return null;
	}

	public BoolHoleType() {
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
		if (obj instanceof BoolHoleType) {
			BoolHoleType et = (BoolHoleType) obj;
			return id.equals(et.id);
		}
		return false;
	}

	public <T> T accept(TypeVisitor<T> visitor) {
		return visitor.visit(this);
	}
}