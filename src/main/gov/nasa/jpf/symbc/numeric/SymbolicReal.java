//
//Copyright (C) 2006 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc.numeric;

import java.util.Map;

public class SymbolicReal extends RealExpression {
	public static double UNDEFINED = Integer.MIN_VALUE+42;
	public double _min = MinMax.MINDOUBLE;
	public double _max = MinMax.MAXDOUBLE;
	public double solution = UNDEFINED; // C
	public double solution_inf = UNDEFINED; // C
	public double solution_sup = UNDEFINED; // C

	static String SYM_REAL_SUFFIX = "_SYMREAL";// C: what is this?
	private String name;

	public SymbolicReal () {
		super();
		PathCondition.flagSolved = false;
	}

	public SymbolicReal (String s) {
		super();
		PathCondition.flagSolved = false;
		name = s;
		//trackedSymVars.add(fixName(name));
	}

	public SymbolicReal (double l, double u) {
		super();
		_min = l;
		_max = u;
		PathCondition.flagSolved = false;
	}

	public SymbolicReal (String s, double l, double u) {
		super();
		_min = l;
		_max = u;
		name = s;
		PathCondition.flagSolved = false;
		//trackedSymVars.add(fixName(name));
	}

	public String getName() {
		return (name != null) ? name : "REAL_" + hashCode();
	}

	public String stringPC () {
		if (!PathCondition.flagSolved) {
			return (name != null) ? name : "REAL_" + hashCode();

		} else {
			return (name != null) ? name + "[" + solution + /* "<" + solution_inf + "," + solution_sup + ">" + */  "]" :
				"REAL_" + hashCode() + "[" + solution + "]";
//			return (name != null) ? name + "[" + solution_inf + "," + solution_sup +  "]" :
//				"REAL_" + hashCode() + "[" + + solution_inf + "," + solution_sup +  "]";
		}
	}

	public String toString () {
		if (!PathCondition.flagSolved) {
			return (name != null) ? name : "REAL_" + hashCode();

		} else {
			return (name != null) ? name + "[" + solution + /* "<" + solution_inf + "," + solution_sup + ">" + */  "]" :
				"REAL_" + hashCode() + "[" + solution + "]";
//			return (name != null) ? name + "[" + solution_inf + "," + solution_sup +  "]" :
//				"REAL_" + hashCode() + "[" + + solution_inf + "," + solution_sup +  "]";
		}
	}


	public double solution() {
		if (PathCondition.flagSolved)
			return solution;
		else
			throw new RuntimeException("## Error: PC not solved!");
	}

    public void getVarsVals(Map<String,Object> varsVals) {
    	varsVals.put(fixName(name), solution);
    }

    private String fixName(String name) {
    	if (name.endsWith(SYM_REAL_SUFFIX)) {
    		name = name.substring(0, name.lastIndexOf(SYM_REAL_SUFFIX));
    	}
    	return name;
    }
}
