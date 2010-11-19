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
// support for arbitrary external functions

import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.RealExpression;

import java.util.Map;
import java.lang.reflect.*;

public class FunctionExpression extends Expression
{
	String class_name;
	String method_name;
	Object[] args;
	Expression [] sym_args;

	public FunctionExpression (String cls, String mth, Object [] as, Expression [] sym_as)
	{
		class_name = cls;
		method_name = mth;
		assert((as == null && sym_as == null) || as.length == sym_as.length);
		// do we need a deep copy here or a shallow copy is enough?
		if (as != null) { // && sym_as!=null) {
			args = new Expression [as.length];
			for (int i=0; i < as.length; i++)
				args[i] = as[i];
		}
	}

	public double solution()
	{
		// here we need to use reflection to invoke the method with
		// name function_name and with parameters the solutions of the arguments

		try {
			  Class<?> cls = Class.forName(class_name);
		      Class<?>[] argTypes = new Class<?>[args.length];
		      for (int i=0; i<args.length; i++)
		        argTypes[i] = args[i].getClass();


		      Method m = cls.getMethod(method_name, argTypes);
		      for (int i=0; i<args.length; i++)
		    	  if (sym_args[i] instanceof IntegerExpression)
			        args[i] = new Integer(((IntegerExpression)sym_args[i]).solution());
			      else // RealExpression
			    	args[i] = new Double(((RealExpression)sym_args[i]).solution());

		      int modifiers = m.getModifiers();
		      if (Modifier.isStatic(modifiers) && Modifier.isPublic(modifiers)){
		        Object result = m.invoke(null, args); // here we need the type of the result
		        System.out.println("result "+result);
		      }
		}

		catch (Throwable e) {
			System.err.println(e);
		}
		return 0.0;
	}

    public void getVarsVals(Map<String,Object> varsVals) {
    	if (sym_args!=null)
    		for (int i = 0; i < sym_args.length; i++)
    			sym_args[i].getVarsVals(varsVals);
    }

	public String stringPC() {
		String result="";
		if (sym_args!=null)
    		for (int i = 0; i < sym_args.length; i++)
    			result = result + sym_args[i].stringPC() + " ";
		return "(" + class_name +"." + method_name + "(" + result + ")";

	}

	public String toString () {
		String result="";
		if (sym_args!=null)
    		for (int i = 0; i < sym_args.length; i++)
    			result = result + sym_args[i].toString() + " ";
		return "(" + class_name +"." + method_name + "(" + result + ")";
	}
}
