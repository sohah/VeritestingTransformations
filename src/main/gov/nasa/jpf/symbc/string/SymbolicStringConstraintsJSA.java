/*  Copyright (C) 2005 United States Government as represented by the
Administrator of the National Aeronautics and Space Administration
(NASA).  All Rights Reserved.

Copyright (C) 2009 Fujitsu Laboratories of America, Inc.

DISCLAIMER OF WARRANTIES AND LIABILITIES; WAIVER AND INDEMNIFICATION

A. No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY
WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY,
INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE
WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM
INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR
FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO
THE SUBJECT SOFTWARE. NO SUPPORT IS WARRANTED TO BE PROVIDED AS IT IS PROVIDED.

B. Waiver and Indemnity: RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS
AGAINST FUJITSU LABORATORIES OF AMERICA AND ANY OF ITS AFFILIATES, THE
UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL
AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE
RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING
FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING
FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY
AND HOLD HARMLESS FUJITSU LABORATORTIES OF AMERICA AND ANY OF ITS AFFILIATES,
THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL
AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE
REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL
TERMINATION OF THIS AGREEMENT. */

package gov.nasa.jpf.symbc.string;

import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import dk.brics.automaton.Automaton;
import dk.brics.string.operations.*;
import java.util.*;

public class SymbolicStringConstraintsJSA {

  StringPathCondition pc = null;
  Map<StringSymbolic,Automaton> symStringVar;
  
  Map<StringSymbolic,Object> activeVars;
  
  Map<StringExpression,Automaton> constraintAutomaton;
  
  public Automaton pb;
 // check satisfiability of string path conditions
  
  public boolean isSatisfiable(StringPathCondition pc) {

		//System.out.println("String Constraint" + pc);

		symStringVar = new HashMap<StringSymbolic,Automaton>();
		constraintAutomaton = new HashMap<StringExpression,Automaton>();
		
		//System.out.println("---------Start---------");
		boolean result =  getExpression(pc.header);
		//System.out.println("---------End---------");
		return result;
	}

  private Automaton getAutomaton(StringSymbolic s) {
  	Automaton a = symStringVar.get(s);
  	if (a == null) {
  			a = Automaton.makeAnyString();
  			symStringVar.put(s, a);  			
  	}
  	activeVars.put(s, new Object());
  	return a;
  }
  
  private void record(StringExpression e, Automaton a) {
  	constraintAutomaton.put(e, a);
  }
  
  private Automaton recall(StringExpression e) {
  	Automaton a = constraintAutomaton.get(e);
  	return a;
  }
  
	private Automaton getStringExpression(StringExpression expr) {
		Automaton result = recall(expr);
		/*
		if (result != null) {
			System.out.println("Found old Expression " + expr);
			return result;
		}
		else*/ 
			result = Automaton.makeAnyString();
		if (expr instanceof StringConstant)
			result = Automaton.makeString(expr.solution());
		else if (expr instanceof StringSymbolic) 
			result = getAutomaton((StringSymbolic)expr);
		else if (expr instanceof DerivedStringExpression) {
			DerivedStringExpression dexpr = (DerivedStringExpression) expr;
			//System.out.println("operator = " + dexpr.op);
			Automaton temp = null;
			switch (dexpr.op) {
			case VALUEOF:
				result = getStringExpression((StringExpression) dexpr.oprlist[0]); // hack not always StringExpression
				break;
			case CONCAT:
				//System.out.println("Found CONCAT " + expr);
				Automaton left = getStringExpression(dexpr.left);
				Automaton right = getStringExpression(dexpr.right);
				result = left.concatenate(right);
				break;
			case SUBSTRING:
				//System.out.println("Found SUBSTRING " + expr);

				// handle special case if everything is concrete
				if (dexpr.oprlist[0] instanceof DerivedStringExpression && dexpr.oprlist[1] instanceof IntegerConstant
						&& (dexpr.oprlist.length == 2 || dexpr.oprlist[2] instanceof IntegerConstant)) {
					int v1 = ((IntegerConstant) dexpr.oprlist[1]).solution();
					int v2 = -1;
					if (dexpr.oprlist.length == 3)
						v2 = ((IntegerConstant) dexpr.oprlist[2]).solution();

					if (((DerivedStringExpression) dexpr.oprlist[0]).left instanceof StringConstant) {
						DerivedStringExpression str = (DerivedStringExpression) dexpr.oprlist[0];
						if (v2 != -1)
							result = Automaton.makeString(((StringConstant) str.left).solution().substring(v2, v1));
						else
							result = Automaton.makeString(((StringConstant) str.left).solution().substring(v1));
					}
				}
				else {
				// something is symbolic so ...
					Expression firstVal = dexpr.oprlist[1];
					Expression secondVal;
					if (dexpr.oprlist.length == 3)
						secondVal = dexpr.oprlist[2];
					// still need to do something with these values if they are symbolic
					temp = getStringExpression((StringExpression) dexpr.oprlist[0]);
					result = (new Substring()).op(temp);
				}
				break;
			case TRIM:
				//System.out.println("Found TRIM " + expr);
				temp = getStringExpression(dexpr.right);
				result = (new Trim()).op(temp);
				break;
			}
		}
		else {
			System.out.println("Differnt type " + expr);
		}
    record (expr, result);
		return result;
	}

	
	private boolean evaluateStringConstraint(StringConstraint c) {		
		Automaton left = null;
		Automaton right = null;
		Automaton intersect = null;
		switch (c.comp) {
		case EQUALS:
		case EQ:	
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			intersect = right.intersection(left);
			post(intersect);
			break;
		case NOTEQUALS:
		case NE:	
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			intersect = right.intersection(left);
			
			if (intersect.isTotal()) {
			// need a corner case for when both strings are completely unconstrained
			// since we need two unconstrained strings to be unequal (as well as equal)				
			  System.out.println("Found Universal Negation");
				post(intersect); // post universal automaton constraint
				//post(intersect.complement());
			}
			else {
				post(intersect.complement());
			}
			break;
		case STARTSWITH:
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			// right is a constant string then we can use commonPrefix
			// else it needs to be an approximation of contains
			if (c.left instanceof StringConstant) { // always left constant if x.startsWith("constant")				
				System.out.println(" Found StartsWith with constant argument ");
				
				String prefixStr = right.getCommonPrefix();
				Automaton rightExtended = Automaton.makeString(prefixStr).concatenate(Automaton.makeAnyString());				
				Automaton leftExtended = left.concatenate(Automaton.makeAnyString());
				
				System.out.println("prefix = '"+ prefixStr + "'");
				System.out.println("left = '"+ leftExtended.getShortestExample(true) + "'");
				System.out.println("prefix intersect left = '" + rightExtended.intersection(leftExtended).getShortestExample(true) + "'");
				
				post(rightExtended.intersection(leftExtended));
			}
			else {
				System.out.println(" Found StartsWith with symbolic argument - approximate by checking containment");
				post(left.intersection(right));
			}
			break;
		case NOTSTARTSWITH:
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			if (c.left instanceof StringConstant) { // always left constant if x.startsWith("constant")
				System.out.println(" Found NotStartsWith with constant argument ");
				
				String prefixStr = right.getCommonPrefix();
				Automaton rightExtended = Automaton.makeString(prefixStr).concatenate(Automaton.makeAnyString());				
				Automaton leftExtended  = left.concatenate(Automaton.makeAnyString());
				
				System.out.println("prefix = '"+ prefixStr + "'");
				System.out.println("left.complement = '"+ left.complement().getShortestExample(true) + "'");
				System.out.println(" is left complement empty? " + left.complement().isEmpty());
				System.out.println("prefix intersect left.complement = '"+ 
						rightExtended.intersection(leftExtended.complement()).getShortestExample(true) + "'");
				
				// we can use left.complement here since we know it is a constant string								
				post(rightExtended.intersection(leftExtended.complement()));
			}
			else {
				System.out.println(" Found NotStartsWith with symbolic argument - approximate by checking containment");
				post(left.intersection(right).complement());
			}			
			break;
		case ENDSWITH:
			System.out.println(" ENDSWITH ");			
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);
			if (c.left instanceof StringConstant) { // always left constant if x.startsWith("constant")
				System.out.println(" Found EndsWith with constant argument ");
				
				left = new Reverse().op(left);
				right = new Reverse().op(right);
				
				String prefixStr = right.getCommonPrefix();
				Automaton rightExtended = Automaton.makeString(prefixStr).concatenate(Automaton.makeAnyString());				
				Automaton leftExtended = left.concatenate(Automaton.makeAnyString());
				
				System.out.println("prefix = '"+ prefixStr + "'");
				System.out.println("left = '"+ leftExtended.getShortestExample(true) + "'");
				System.out.println("prefix intersect left = '" + rightExtended.intersection(leftExtended).getShortestExample(true) + "'");
				
				post(rightExtended.intersection(leftExtended));
			} 
			else {
				post(left.intersection(right));
			}
			break;
		case NOTENDSWITH:
			System.out.println(" NOTENDSWITH ");
			left = getStringExpression(c.left);
			right = getStringExpression(c.right);			
			if (c.left instanceof StringConstant) { // always left constant if x.startsWith("constant")
				System.out.println(" Found NotEndsWith with constant argument ");
				
				left = new Reverse().op(left);
				right = new Reverse().op(right);				
				
				String prefixStr = right.getCommonPrefix();
				Automaton rightExtended = Automaton.makeString(prefixStr).concatenate(Automaton.makeAnyString());				
				Automaton leftExtended  = left.concatenate(Automaton.makeAnyString());
				
				System.out.println("prefix = '"+ prefixStr + "'");
				System.out.println("left.complement = '"+ left.complement().getShortestExample(true) + "'");
				System.out.println(" is left complement empty? " + left.complement().isEmpty());
				System.out.println("prefix intersect left.complement = '"+ 
						rightExtended.intersection(leftExtended.complement()).getShortestExample(true) + "'");
				
				// we can use left.complement here since we know it is a constant string				
				post(rightExtended.intersection(leftExtended.complement()));
			}
			else {			
				post(left.intersection(right).complement());
			}
			break;
		}		
		return checkConstraint();
	}

	private void post(Automaton constraint) {
		
		Map<StringSymbolic,Automaton> varsToUpdate = new HashMap<StringSymbolic,Automaton>();
		
		System.out.println("---Post Start---");
		
		for(Map.Entry<StringSymbolic, Automaton> entry : symStringVar.entrySet()) {
			StringSymbolic sym = entry.getKey();
			Automaton var = entry.getValue();
			if (!activeVars.containsKey(sym)) {
				System.out.println("Skipping inactive symbolic variable" + sym);
				continue;
			}
			var = constraint.intersection(var);
			varsToUpdate.put(sym, var);
			sym.solution = var.getShortestExample(true);
			System.out.println(sym.getName() + " post value is '" + var.getShortestExample(true) + "'");
		}
		for (Map.Entry<StringSymbolic, Automaton> entry : varsToUpdate.entrySet()) {
			StringSymbolic sym = entry.getKey();
			Automaton var = entry.getValue();
			symStringVar.put(sym, var);
		}
		pb = constraint;
		
		System.out.println("---Post End---");
	}

	private boolean checkConstraint() {
		boolean constraintResult = !pb.isEmpty();
		if (constraintResult) {
			System.out.println("POS: Solution '" + pb.getShortestExample(true) + "'");
			printSolution();
		}
		else {
			System.out.println("String Constraint is UnSAT");
		}
		return constraintResult;
	}
	
	private boolean getExpression(StringConstraint c) {
		while (c != null) {
			
			activeVars = new HashMap<StringSymbolic,Object>();
			boolean constraintResult = evaluateStringConstraint(c);
												
			if (constraintResult == false) 
				return false;
			
			c = c.and;
		}
		
		return true;
	}

	private void printSolution() {
		for(Map.Entry<StringSymbolic, Automaton> entry : symStringVar.entrySet()) {
			StringSymbolic sym = entry.getKey();
			Automaton var = entry.getValue();
			sym.solution = var.getShortestExample(true);
			System.out.println(sym.getName() + " value is '" + var.getShortestExample(true) + "'");
		}
	}
	
	public void solve(StringPathCondition pc) {

	}

}