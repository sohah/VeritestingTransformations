package gov.nasa.jpf.symbc.strings;

public class SymbolicString extends StringExpression {
	private String name;
	public String solution = "UNDEFINED";

	public SymbolicString () {
		super();
	}

	public SymbolicString (String s) {
		super();
		name = s;

	}

	public String getName() {
		return (name != null) ? name : "STRING_" + hashCode();
	}

	public String toString () {
		if (!StringPathCondition.flagSolved) {
			return (name != null) ? name : "STRING_" + hashCode();

		} else {
			return (name != null) ? name + "[" + solution + "]" :
				"STRING_" + hashCode() + "[" + solution + "]";
		}
	}
}
