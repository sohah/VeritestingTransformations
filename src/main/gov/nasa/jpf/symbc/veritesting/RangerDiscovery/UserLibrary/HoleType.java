package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.UserLibrary;


import jkind.lustre.Location;
import jkind.lustre.Type;


public class HoleType extends Type {
	public final String id  = "hole";

	public HoleType(Location location) {
		super(location);
	}

	@Override
	public <T> T accept(jkind.lustre.visitors.TypeVisitor<T> visitor) {
		return null;
	}

	public HoleType() {
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
		if (obj instanceof HoleType) {
			HoleType et = (HoleType) obj;
			return id.equals(et.id);
		}
		return false;
	}

	public <T> T accept(TypeVisitor<T> visitor) {
		return visitor.visit(this);
	}
}