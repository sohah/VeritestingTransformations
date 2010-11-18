//
//Copyright (C) 2005 United States Government as represented by the
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

package gov.nasa.jpf.symbc.concolic;
// supports math lib

import gov.nasa.jpf.symbc.numeric.Expression;

import java.util.Map;


public class FunctionExpression extends Expression
{
	Expression [] args;
	String   function_name; // should be fully qualified

	public FunctionExpression (String fun, Expression [] as)
	{
		function_name = fun;

		// do we need a deep copy here or a shallow copy is enough?
		if (as!=null) {
			args = new Expression [as.length];
			for (int i=0; i < as.length; i++)
				args[i] = as[i];
		}
	}

	public double solution()
	{
		// here we need to use reflection to invoke the method with
		// name function_name and with parameters the solutions of the arguments

		Class c;
		return 0.0;

	}

    public void getVarsVals(Map<String,Object> varsVals) {
//    	if (arg1 != null) arg1.getVarsVals(varsVals);
//    	if (arg2 != null) arg2.getVarsVals(varsVals);
    }

	public String stringPC() {
		return "";
//		if (op == Function.SIN || op == Function.COS ||
//			op == Function.ROUND || op == Function.EXP ||
//			op == Function.ASIN || op == Function.ACOS ||
//			op == Function.ATAN || op == Function.LOG ||
//			op == Function.TAN || op == Function.SQRT)
//			return "(" + op.toString() + "(" + arg1.stringPC() + "))";
//		else //op == MathFunction.POW || op == MathFunction.ATAN2
//			return "(" + op.toString() + "(" + arg1.stringPC() + "," + arg2.stringPC() + "))";
	}

	public String toString () {
		return "";
//		if (op == Function.SIN || op == Function.COS ||
//				op == Function.ROUND || op == Function.EXP ||
//				op == Function.ASIN || op == Function.ACOS ||
//				op == Function.ATAN || op == Function.LOG ||
//				op == Function.TAN || op == Function.SQRT)
//			return  op.toString() + "(" + arg1.toString() + ")";
//		else //op == MathFunction.POW || op == MathFunction.ATAN2
//			return  op.toString() + "(" + arg1.toString() + "," + arg2.toString() + ")";
	}
}
