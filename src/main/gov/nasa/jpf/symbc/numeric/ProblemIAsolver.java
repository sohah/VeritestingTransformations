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

import ia_math.RealInterval;
import ia_parser.Exp;
import ia_parser.IAParser;
import ia_parser.RealIntervalTable;
//import ia_parser.sym;

public class ProblemIAsolver extends ProblemGeneral {
	String pb;
	String format = "%20.10f";

	public ProblemIAsolver() {
		pb = "";
	}

	String makeIntVar(String name, int min, int max) {
		pb = pb + name + " >= " + min + "; "+ name + " <= " + max + "; ";
		return name;
	}

	String makeRealVar(String name, double min, double max) {
		pb = pb + name + " >= " + min + "; "+ name + " <= " + max + "; ";
		return name;
	}

	Object eq(int value, Object exp){return  value + " = " + (String)exp + "; ";}
	Object eq(Object exp, int value){return  (String)exp + " = " + value + "; ";}
	Object eq(Object exp1, Object exp2){
		return  (String)exp1 + " = " + (String)exp2 + "; ";
	}
	// could be a problem here with the number format
	Object eq(double value, Object exp){return  String.format(format,value) + " = " + (String)exp + "; ";}
	Object eq(Object exp, double value){return  (String)exp + " = " + String.format(format,value) + "; ";}

	Object neq(int value, Object exp){return  value + " != " + (String)exp + "; ";}
	Object neq(Object exp, int value){return  (String)exp + " != " + value + "; ";}
	Object neq(Object exp1, Object exp2){
		return  (String)exp1 + " != " + (String)exp2 + "; ";
	}
	Object neq(double value, Object exp){return  String.format(format,value) + " != " + (String)exp + "; ";}
	Object neq(Object exp, double value){return  (String)exp + " != " + String.format(format,value) + "; ";}


	Object leq(int value, Object exp){return  value + " <= " + (String)exp + "; ";}
	Object leq(Object exp, int value){return  (String)exp + " <= " + value + "; ";}
	Object leq(Object exp1, Object exp2){
		return  (String)exp1 + " <= " + (String)exp2 + "; ";
	}
	Object leq(double value, Object exp){return  String.format(format,value) + " <= " + (String)exp + "; ";}
	Object leq(Object exp, double value){return  (String)exp + " <= " + String.format(format,value) + "; ";}

	Object geq(int value, Object exp){return  value + " >= " + (String)exp + "; ";}
	Object geq(Object exp, int value){return  (String)exp + " >= " + value + "; ";}
	Object geq(Object exp1, Object exp2){
		return  (String)exp1 + " >= " + (String)exp2 + "; ";
	}
	Object geq(double value, Object exp){return  String.format(format,value) + " >= " + (String)exp + "; ";}
	Object geq(Object exp, double value){return  (String)exp + " >= " + String.format(format,value) + "; ";}

	Object lt(int value, Object exp){return  value + " < " + (String)exp + "; ";}
	Object lt(Object exp, int value){return  (String)exp + " < " + value + "; ";}
	Object lt(Object exp1, Object exp2){
		return  (String)exp1 + " < " + (String)exp2 + "; ";
	}
	Object lt(double value, Object exp){return  String.format(format,value) + " < " + (String)exp + "; ";}
	Object lt(Object exp, double value){return  (String)exp + " < " + String.format(format,value) + "; ";}


	Object gt(int value, Object exp){return  value + " > " + (String)exp + "; ";}
	Object gt(Object exp, int value){return  (String)exp + " > " + value + "; ";}
	Object gt(Object exp1, Object exp2){
		return  (String)exp1 + " > " + (String)exp2 + "; ";
	}
	Object gt(double value, Object exp){return  String.format(format,value) + " > " + (String)exp + "; ";}
	Object gt(Object exp, double value){return  (String)exp + " > " + String.format(format,value) + "; ";}

	Object plus(int value, Object exp) {return  "("+value + "+" + exp +")" ;}
	Object plus(Object exp, int value) {return  "("+exp + "+" + value +")" ;}
	Object plus(Object exp1, Object exp2) {return  "("+exp1 + "+" + exp2 +")" ;}
	Object plus(double value, Object exp) {return  "("+String.format(format,value) + "+" + exp +")" ;}
	Object plus(Object exp, double value) {return  "("+exp + "+" + String.format(format,value) +")" ;}

	Object minus(int value, Object exp) {return  "("+value + "-" + exp +")" ;}
	Object minus(Object exp, int value) {return  "("+exp + "-" + value +")" ;}
	Object minus(Object exp1, Object exp2) {return  "("+exp1 + "-" + exp2 +")" ;}
	Object minus(double value, Object exp) {return  "("+String.format(format,value) + "-" + exp +")" ;}
	Object minus(Object exp, double value) {return  "("+exp + "-" + String.format(format,value) +")" ;}

	Object mult(int value, Object exp) {return  "("+value + "*" + exp +")" ;}
	Object mult(Object exp, int value) {return  "("+exp + "*" + value +")" ;}
	Object mult(Object exp1, Object exp2) {return  "("+exp1 + "*" + exp2 +")" ;}
	Object mult(double value, Object exp) {return  "("+String.format(format,value) + "*" + exp +")" ;}
	Object mult(Object exp, double value) {return  "("+exp + "*" + String.format(format,value) +")" ;}

	Object div(int value, Object exp) {return  "("+value + "/" + exp +")" ;}
	Object div(Object exp, int value) {return  "("+exp + "/" + value +")" ;}
	Object div(Object exp1, Object exp2) {return  "("+exp1 + "/" + exp2 +")" ;}
	Object div(double value, Object exp) {return  "("+String.format(format,value) + "/" + exp +")" ;}
	Object div(Object exp, double value) {return  "("+exp + "/" + String.format(format,value) +")" ;}


	Object sin(Object exp) {
		return "sin("+exp+")";
	}
	Object cos(Object exp) {
		return "cos("+exp+")";
	}

	Object power(Object exp1, Object exp2) {
		//return "("+exp1+"**"+exp2+")";
		return "("+exp1+"^"+exp2+")"; // TODO: to ask Hank about the difference between ** and ^
	}

	Object power(Object exp1, double exp2) {
		//return "("+exp1+"**"+exp2+")";
		return "("+exp1+"^"+exp2+")"; // TODO: to ask Hank about the difference between ** and ^
	}

	Object power(double exp1, Object exp2) {
		//return "("+exp1+"**"+exp2+")";
		return "("+exp1+"^"+exp2+")"; // TODO: to ask Hank about the difference between ** and ^
	}

	Object sqrt(Object exp) {
		//return "("+exp1+"**"+exp2+")";
		// TODO: add test exp >=0
		return "("+exp+"^"+0.5+")"; // TODO: to ask Hank about the difference between ** and ^
	}

	Object exp(Object exp) {
		return "exp("+exp+")";
	}

	Object asin(Object exp) {
		return "asin("+exp+")";
	}
	Object acos(Object exp) {
		return "acos("+exp+")";
	}
	Object atan(Object exp) {
		return "atan("+exp+")";
	}
	Object log(Object exp) {
		return "log("+exp+")";
	}
	Object tan(Object exp) {
		return "tan("+exp+")";
	}
	Object mixed(Object exp1, Object exp2) {
		return (String)exp1 + " = " + (String)exp2 + "; ";
	}

	// IASolver specific
	RealIntervalTable vars;
	boolean narrow(Exp exp, int numNarrows) {
		vars = new RealIntervalTable();
		exp.bindVars(vars);
		for (int i = 0; i <= numNarrows; i++) {
			if (!exp.narrow()) {
				//System.out.println("narrow failed");
				return false;
			}
		}
//		String var_string = "";
//		for (int j = 0; j < vars.size(); j++)
//			var_string = var_string + "  " + vars.getEnvPairString2(j) + "\n";
//		System.out.println("narrow succeeded"+ var_string);
		return true;
	}

	// TODO: maybe cut chooseValue: not used
	static double chooseValue(RealInterval interval) {
		double lo = interval.lo();
		double hi = interval.hi();
		double chosen;

		if (Double.isInfinite(lo)) {
			if (Double.isInfinite(hi)) {
				chosen = 1.12;
			} else {
				chosen = hi - 1.0;
			}
		} else {
			if (Double.isInfinite(hi)) {
				chosen = lo + 1.0;
			} else {
				chosen = (hi + lo) / 2.0;
			}
		}
		return chosen;
	}


	double getRealValueInf(Object dpVar) {
		assert(vars != null && dpVar !=null);
		return vars.lookup((String)dpVar).lo();
	}

	double getRealValueSup(Object dpVar) {
		assert(vars != null && dpVar !=null);
		return vars.lookup((String)dpVar).hi();
	}
	double getRealValue(Object dpVar) {
		throw new RuntimeException("# Error: IASolver can not compute real solution!");
	}

	int getIntValue(Object dpVar) {
		throw new RuntimeException("# Error: IASolver can not compute int solution!");
	}

	Boolean solve() {
		String c = pb;
		if(c==null || c=="")
			return true;
		try {
			int max_narrow = 100;// TODO: play with different values for max_narrow;

			// Solve the original system
			//System.out.println(" PARSE: "+c);
			Exp exp = IAParser.parseString(c);
			return narrow(exp, max_narrow);

		} catch (Exception parse_exception) {
			parse_exception.printStackTrace();
			throw new RuntimeException("## Error IASolver: "+pb);//parse_exception);
		}
	}

	void post(Object constraint) {
		pb = pb + constraint;
	}

	Object and(int value, Object exp) {
		throw new RuntimeException("## Error IASolver does not support bitwise AND");
	}

	Object and(Object exp, int value) {
		throw new RuntimeException("## Error IASolver does not support bitwise AND");
	}

	Object and(Object exp1, Object exp2) {
		throw new RuntimeException("## Error IASolver does not support bitwise AND");
	}

	@Override
	Object or(int value, Object exp) {
		throw new RuntimeException("## Error IASolver does not support bitwise OR");
	}

	@Override
	Object or(Object exp, int value) {
		throw new RuntimeException("## Error IASolver does not support bitwise OR");
	}

	@Override
	Object or(Object exp1, Object exp2) {
		throw new RuntimeException("## Error IASolver does not support bitwise OR");
	}

	@Override
	Object shiftL(int value, Object exp) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Object shiftL(Object exp, int value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Object shiftR(int value, Object exp) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Object shiftR(Object exp, int value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Object xor(int value, Object exp) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Object xor(Object exp, int value) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Object xor(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		return null;
	}

	

}
