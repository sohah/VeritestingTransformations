package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.UserLibrary;


public interface TypeVisitor<T> extends jkind.lustre.visitors.TypeVisitor{
	public T visit(HoleType e);
}
