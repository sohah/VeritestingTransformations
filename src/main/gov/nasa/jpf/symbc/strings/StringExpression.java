package gov.nasa.jpf.symbc.strings;

public abstract class StringExpression {
	public String solution() {
		throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
	}
}
