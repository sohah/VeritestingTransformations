package gov.nasa.jpf.symbc.strings;

public class StringConstant extends StringExpression{
	private String value;

	  public StringConstant (String v) {
	    value = v;
	  }

	  public String toString () {
		    return "CONST_" + value + "";
	  }

	  public String value () {
		    return value;
	  }

	  public String solution() {
		  	return value;
	  }

	  public boolean equals (Object o) {
		  if (!(o instanceof StringConstant)) {
			  return false;
		  }
		  return value == ((StringConstant) o).value;
	  }
}
