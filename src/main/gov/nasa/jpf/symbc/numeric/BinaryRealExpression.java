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

package gov.nasa.jpf.symbc.numeric;

import java.util.Map;

public class BinaryRealExpression extends RealExpression 
{
	RealExpression left;
	Operator   op;
	RealExpression right;

	public BinaryRealExpression (RealExpression l, Operator o, RealExpression r) 
	{
		left = l;
		op = o;
		right = r;
	}

	public double solution() 
	{
		double l = left.solution();
		double r = right.solution();
		switch(op){
		   case PLUS:  return l + r;
		   case MINUS: return l - r;
		   case MUL:   return l * r;
		   case DIV:   assert(r!=0);
			           return l/r;
           default:    throw new RuntimeException("## Error: BinaryRealSolution solution: l " + l + " op " + op + " r " + r);
		}
	}

    public void getVarsVals(Map<String,Object> varsVals) {
    	left.getVarsVals(varsVals);
    	right.getVarsVals(varsVals);
    }
	
	public String stringPC() {
		return "(" + left.stringPC() + op.toString() + right.stringPC() + ")";
	}

	public String toString () 
	{
		return "(" + left.toString() + op.toString() + right.toString() + ")";
	}

	public Operator getOp() {
		return op;
	}

	public RealExpression getLeft() {
		return left;
	}

	public RealExpression getRight() {
		return right;
	}
}
