import java.util.Map;
import java.util.Iterator;

import soot.Body;
import soot.Unit;
import soot.jimple.*;
import soot.shimple.*;
import soot.BodyTransformer;
import soot.G;
import soot.PackManager;
import soot.Transform;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.Type;
import soot.Value;



class MyUtils {
	public static final int maxSuccSteps = 10;

	public static final String nCNLIE = "new ComplexNonLinearIntegerExpression(";
	public static int pathCounter=0;

	public static final int getPathCounter() { pathCounter++; return pathCounter; }

	public static final String SPFLogicalAnd(String e1, String e2) {
		return nCNLIE + e1 + ", LOGICAL_AND, " + e2 + ")";
	}

	public static final String SPFLogicalOr(String e1, String e2) {
		return nCNLIE + e1 + ", LOGICAL_OR, " + e2 + ")";
	}
	
	public static final Boolean isIntegerConstant(Value v) {
	// https://stackoverflow.com/questions/5439529/determine-if-a-string-is-an-integer-in-java
		try { Integer.parseInt(v.toString()); }
		catch (NumberFormatException e) { return false; }
		catch (NullPointerException e) { return false; }
		return true;
	}
}
