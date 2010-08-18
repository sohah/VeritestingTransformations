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



import gov.nasa.jpf.symbc.SymbolicInstructionFactory;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

//import choco.Problem;
import choco.integer.*;
import choco.real.*;
import choco.real.constraint.MixedEqXY;

public class SymbolicConstraintsChoco {
	  RealProblem pb;
	  Map<SymbolicReal, RealVar>	symRealVar; // a map between symbolic real variables and choco variables
	  Map<SymbolicInteger,IntDomainVar>	symIntegerVar; // a map between symbolic variables and choco variables
	  Boolean result; // tells whether result is satisfiable or not

	  
	  //	 Converts IntegerExpression's into Choco IntExp's
	  IntExp getExpression(IntegerExpression eRef) {
			assert eRef != null;
			assert !(eRef instanceof IntegerConstant);

			if (eRef instanceof SymbolicInteger) {
				IntDomainVar choco_var = symIntegerVar.get(eRef);
				if (choco_var == null) {
					choco_var = pb.makeBoundIntVar(((SymbolicInteger)eRef).getName(), 
							((SymbolicInteger)eRef)._min, ((SymbolicInteger)eRef)._max);
					symIntegerVar.put((SymbolicInteger)eRef, choco_var);
				}
				return choco_var;
			}

			Operator    opRef;
			IntegerExpression	e_leftRef;
			IntegerExpression	e_rightRef;

			if(eRef instanceof BinaryLinearIntegerExpression) {
				opRef = ((BinaryLinearIntegerExpression)eRef).op;
				e_leftRef = ((BinaryLinearIntegerExpression)eRef).left;
				e_rightRef = ((BinaryLinearIntegerExpression)eRef).right;

				switch(opRef){
				   case PLUS:
						if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
							throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
						else if (e_leftRef instanceof IntegerConstant)
							return pb.plus(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
						else if (e_rightRef instanceof IntegerConstant)
							return pb.plus(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
						else
							return pb.plus(getExpression(e_leftRef),getExpression(e_rightRef));
				   case MINUS:
					   if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
							throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
						else if (e_leftRef instanceof IntegerConstant)
							return pb.minus(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
						else if (e_rightRef instanceof IntegerConstant)
							return pb.minus(getExpression(e_leftRef),((IntegerConstant)e_rightRef).value);
						else
							return pb.minus(getExpression(e_leftRef),getExpression(e_rightRef));
				   case MUL:
					   if (e_leftRef instanceof IntegerConstant && e_rightRef instanceof IntegerConstant)
							throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
						else if (e_leftRef instanceof IntegerConstant)
							return pb.mult(((IntegerConstant)e_leftRef).value,getExpression(e_rightRef));
						else if (e_rightRef instanceof IntegerConstant)
							return pb.mult(((IntegerConstant)e_rightRef).value,getExpression(e_leftRef));
						else
							throw new RuntimeException("## Error: Binary Non Linear Operation");   
				   case DIV:
					   throw new RuntimeException("## Error: Binary Non Linear Operation"); 
				   default:
					   throw new RuntimeException("## Error: Binary Non Linear Operation"); 
				}
			}
			else {
				throw new RuntimeException("## Error: Binary Non Linear Expression " + eRef);
			}
		}
	  
	  
	// Converts RealExpression's into Choco RealExp's
	RealExp getExpression(RealExpression eRef) {
		assert eRef != null;
		assert !(eRef instanceof RealConstant);

		if (eRef instanceof SymbolicReal) {
			RealVar choco_var = symRealVar.get(eRef);
			if (choco_var == null) {
				choco_var = pb.makeRealVar(((SymbolicReal)eRef).getName(), 
						((SymbolicReal)eRef)._min, ((SymbolicReal)eRef)._max);
				symRealVar.put((SymbolicReal)eRef, choco_var);
			}
			return choco_var;
		}

		Operator    opRef;
		RealExpression	e_leftRef;
		RealExpression	e_rightRef;
	
		MathFunction funRef;
		RealExpression	e_arg1Ref, e_arg2Ref;
		
		if(eRef instanceof BinaryRealExpression) {
			opRef = ((BinaryRealExpression)eRef).op;
			e_leftRef = ((BinaryRealExpression)eRef).left;
			e_rightRef = ((BinaryRealExpression)eRef).right;

			switch(opRef){
			case PLUS:
				if (e_leftRef instanceof RealConstant && e_rightRef instanceof RealConstant)
					throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
				else if (e_leftRef instanceof RealConstant)
					return pb.plus(pb.cst(((RealConstant)e_leftRef).value), getExpression(e_rightRef));
				else if (e_rightRef instanceof RealConstant)
					return pb.plus(getExpression(e_leftRef),pb.cst(((RealConstant)e_rightRef).value));
				else
					return pb.plus(getExpression(e_leftRef),getExpression(e_rightRef));
			case MINUS:
				if (e_leftRef instanceof RealConstant && e_rightRef instanceof RealConstant)
					throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
				else if (e_leftRef instanceof RealConstant)
					return pb.minus(pb.cst(((RealConstant)e_leftRef).value),getExpression(e_rightRef));
				else if (e_rightRef instanceof RealConstant)
					return pb.minus(getExpression(e_leftRef),pb.cst(((RealConstant)e_rightRef).value));
				else
					return pb.minus(getExpression(e_leftRef),getExpression(e_rightRef));
			case MUL:
				if (e_leftRef instanceof RealConstant && e_rightRef instanceof RealConstant)
					throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
				else if (e_leftRef instanceof RealConstant)
					return pb.mult(pb.cst(((RealConstant)e_leftRef).value),getExpression(e_rightRef));
				else if (e_rightRef instanceof RealConstant)
					return pb.mult(pb.cst(((RealConstant)e_rightRef).value),getExpression(e_leftRef));
				else
					return pb.mult(getExpression(e_leftRef),getExpression(e_rightRef));
			case DIV:
				if (e_leftRef instanceof RealConstant && e_rightRef instanceof RealConstant)
					throw new RuntimeException("## Error: this is not a symbolic expression"); // TODO: fix
				else if (e_leftRef instanceof RealConstant)
					return pb.div(pb.cst(((RealConstant)e_leftRef).value),getExpression(e_rightRef));
				else if (e_rightRef instanceof RealConstant)
					return pb.div(getExpression(e_leftRef),((RealConstant)e_rightRef).value);
				else
					return pb.div(getExpression(e_leftRef),getExpression(e_rightRef));
			default:
				throw new RuntimeException("## Error: Expression " + eRef);
			}
		}
		else if(eRef instanceof MathRealExpression) {
			funRef = ((MathRealExpression)eRef).op;
			e_arg1Ref = ((MathRealExpression)eRef).arg1;
			e_arg2Ref = ((MathRealExpression)eRef).arg2;
			switch(funRef){
			case SIN: return pb.sin(getExpression(e_arg1Ref));
			case COS: return pb.cos(getExpression(e_arg1Ref));
			case POW: {
				if (e_arg2Ref instanceof RealConstant)
					return pb.power(getExpression(e_arg1Ref),(int)((RealConstant)e_arg2Ref).value);
			}
			default:
				throw new RuntimeException("## Error: Expression " + eRef);	
			}	
		}
		else
			throw new RuntimeException("## Error: Expression " + eRef);
	}
	
	boolean createChocoMixedConstraint(MixedConstraint cRef) {
		
		Comparator c_compRef = cRef.getComparator();
		RealExpression c_leftRef = (RealExpression)cRef.getLeft();
		IntegerExpression c_rightRef = (IntegerExpression)cRef.getRight();
		assert (c_compRef == Comparator.EQ);
		
		if (c_leftRef instanceof SymbolicReal && c_rightRef instanceof SymbolicInteger) {
			pb.post(new MixedEqXY((RealVar)(getExpression(c_leftRef)),(IntDomainVar)(getExpression(c_rightRef))));
		}
		else if (c_leftRef instanceof SymbolicReal) { // c_rightRef is an IntegerExpression
			IntDomainVar tmpi = pb.makeBoundIntVar(c_rightRef + "_" + c_rightRef.hashCode(),(int)(((SymbolicReal)c_leftRef)._min), (int)(((SymbolicReal)c_leftRef)._max));
			pb.post(pb.eq(getExpression(c_rightRef),tmpi));
		    pb.post(new MixedEqXY((RealVar)(getExpression(c_leftRef)),tmpi));
			
		}
		else if (c_rightRef instanceof SymbolicInteger) { // c_leftRef is a RealExpression
			RealVar tmpr = pb.makeRealVar(c_leftRef + "_" + c_leftRef.hashCode(), ((SymbolicInteger)c_rightRef)._min, ((SymbolicInteger)c_rightRef)._max);
			pb.post(pb.eq(tmpr, getExpression(c_leftRef)));
		    pb.post(new MixedEqXY(tmpr,(IntDomainVar)(getExpression(c_rightRef))));
		}
		else	
			assert(false); // should not be reachable
		return true;
	}
	
	boolean createChocoRealConstraint(RealConstraint cRef) {
		
		Comparator c_compRef = cRef.getComparator();
		RealExpression c_leftRef = (RealExpression)cRef.getLeft();
		RealExpression c_rightRef = (RealExpression)cRef.getRight();
		
		switch(c_compRef){
		case EQ:
			if (c_leftRef instanceof RealConstant && c_rightRef instanceof RealConstant) {
				if (!(((RealConstant) c_leftRef).value == ((RealConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof RealConstant) {
				pb.post(pb.eq(((RealConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof RealConstant) {
				pb.post(pb.eq(getExpression(c_leftRef),((RealConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.eq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case NE:
			if (c_leftRef instanceof RealConstant && c_rightRef instanceof RealConstant) {
				if (!(((RealConstant) c_leftRef).value != ((RealConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof RealConstant) {
				pb.post(pb.neq(((RealConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof RealConstant) {
				pb.post(pb.neq(getExpression(c_leftRef),((RealConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.neq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case LT:
			if (c_leftRef instanceof RealConstant && c_rightRef instanceof RealConstant) {
				if (!(((RealConstant) c_leftRef).value < ((RealConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof RealConstant) {
				pb.post(pb.lt(((RealConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof RealConstant) {
				pb.post(pb.lt(getExpression(c_leftRef),((RealConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.lt(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case GE:
			if (c_leftRef instanceof RealConstant && c_rightRef instanceof RealConstant) {
				if (!(((RealConstant) c_leftRef).value >= ((RealConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof RealConstant) {
				pb.post(pb.geq(((RealConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof RealConstant) {
				pb.post(pb.geq(getExpression(c_leftRef),((RealConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.geq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case LE:
			if (c_leftRef instanceof RealConstant && c_rightRef instanceof RealConstant) {
				if (!(((RealConstant) c_leftRef).value <= ((RealConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof RealConstant) {
				pb.post(pb.leq(((RealConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof RealConstant) {
				pb.post(pb.leq(getExpression(c_leftRef),((RealConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.leq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case GT:
			if (c_leftRef instanceof RealConstant && c_rightRef instanceof RealConstant) {
				if (!(((RealConstant) c_leftRef).value > ((RealConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof RealConstant) {
				pb.post(pb.gt(((RealConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof RealConstant) {
				pb.post(pb.gt(getExpression(c_leftRef),((RealConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.gt(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		}
		return true;
	}
	
	boolean createChocoLinearIntegerConstraint(LinearIntegerConstraint cRef) {
		
		Comparator c_compRef = cRef.getComparator();

		IntegerExpression c_leftRef = (IntegerExpression)cRef.getLeft();
		IntegerExpression c_rightRef = (IntegerExpression)cRef.getRight();

		switch(c_compRef){
		case EQ: 
			if (c_leftRef instanceof IntegerConstant && c_rightRef instanceof IntegerConstant) {
				if (!(((IntegerConstant) c_leftRef).value == ((IntegerConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof IntegerConstant) {
				pb.post(pb.eq(((IntegerConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof IntegerConstant) {
				pb.post(pb.eq(getExpression(c_leftRef),((IntegerConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.eq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case NE:
			if (c_leftRef instanceof IntegerConstant && c_rightRef instanceof IntegerConstant) {
				if (!(((IntegerConstant) c_leftRef).value != ((IntegerConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof IntegerConstant) {
				pb.post(pb.neq(((IntegerConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof IntegerConstant) {
				pb.post(pb.neq(getExpression(c_leftRef),((IntegerConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.neq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case LT:
			if (c_leftRef instanceof IntegerConstant && c_rightRef instanceof IntegerConstant) {
				if (!(((IntegerConstant) c_leftRef).value < ((IntegerConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof IntegerConstant) {
				pb.post(pb.lt(((IntegerConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof IntegerConstant) {
				pb.post(pb.lt(getExpression(c_leftRef),((IntegerConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.lt(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case GE:
			if (c_leftRef instanceof IntegerConstant && c_rightRef instanceof IntegerConstant) {
				if (!(((IntegerConstant) c_leftRef).value >= ((IntegerConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof IntegerConstant) {
				pb.post(pb.geq(((IntegerConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof IntegerConstant) {
				pb.post(pb.geq(getExpression(c_leftRef),((IntegerConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.geq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case LE:
			if (c_leftRef instanceof IntegerConstant && c_rightRef instanceof IntegerConstant) {
				if (!(((IntegerConstant) c_leftRef).value <= ((IntegerConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof IntegerConstant) {
				pb.post(pb.leq(((IntegerConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof IntegerConstant) {
				pb.post(pb.leq(getExpression(c_leftRef),((IntegerConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.leq(getExpression(c_leftRef),getExpression(c_rightRef)));
			break;
		case GT:
			if (c_leftRef instanceof IntegerConstant && c_rightRef instanceof IntegerConstant) {
				if (!(((IntegerConstant) c_leftRef).value > ((IntegerConstant) c_rightRef).value))
					return false;
				else
					return true;
			}
			else if (c_leftRef instanceof IntegerConstant) {
				pb.post(pb.gt(((IntegerConstant)c_leftRef).value,getExpression(c_rightRef)));
			}
			else if (c_rightRef instanceof IntegerConstant) {
				pb.post(pb.gt(getExpression(c_leftRef),((IntegerConstant)c_rightRef).value));
			}
			else	
				pb.post(pb.gt(getExpression(c_leftRef),getExpression(c_rightRef)));			
			break;
		}
		return true;
	}
	
	public boolean isSatisfiable(PathCondition pc) {
		
		pb = new RealProblem();
		//pb.setPrecision(1e-8);// need to check this
		symRealVar = new HashMap<SymbolicReal,RealVar>();
		symIntegerVar = new HashMap<SymbolicInteger,IntDomainVar>();
		//result = null;
				
		if (pc == null) {
			if (SymbolicInstructionFactory.debugMode) 
				System.out.println("## Warning: empty path condition");
			return true;
		}

		Constraint cRef = pc.header;

		while (cRef != null) { 
			boolean constraintResult = true;
			
			if (cRef instanceof RealConstraint)
				constraintResult= createChocoRealConstraint((RealConstraint)cRef);// create choco real constraint
			else if (cRef instanceof LinearIntegerConstraint)
				constraintResult= createChocoLinearIntegerConstraint((LinearIntegerConstraint)cRef);// create choco linear integer constraint
			else if (cRef instanceof MixedConstraint)
				// System.out.println("Mixed Constraint");
				constraintResult= createChocoMixedConstraint((MixedConstraint)cRef);
			else 
				throw new RuntimeException("## Error: Non Linear Integer Constraint not handled " + cRef);
			
			if(constraintResult == false) return false;
			
			cRef = cRef.and;
		}
		
		//pb.getSolver().setTimeLimit(30000);
		
		result = pb.solve();
		if(result == null) {
			if (SymbolicInstructionFactory.debugMode)
				System.out.println("## Warning: don't know (returned PC not-satisfiable)");
			return false;
		}
		
		return (result == Boolean.TRUE ? true : false);
	}

	
	public void solve(PathCondition pc) {
		if(isSatisfiable(pc)) {

			// compute solutions for real variables: 
			//    For each variable Xi:
			//       Choose a value Vi for Xi from its range 
			//       Add "Xi == Vi" to the Choco problem
			//       Resolve the Choco problem to get new ranges of values for the remaining variables.
			Boolean isSolvable = true;
			Set<Entry<SymbolicReal,RealVar>> sym_realvar_mappings = symRealVar.entrySet();
			Iterator<Entry<SymbolicReal,RealVar>> i_real = sym_realvar_mappings.iterator();
			while(i_real.hasNext() && isSolvable) {
				Entry<SymbolicReal,RealVar> e = i_real.next();
				SymbolicReal pcVar = e.getKey();
				RealVar chocoVar = e.getValue();
				pcVar.solution_inf=chocoVar.getValue().getInf();
				pcVar.solution_sup=chocoVar.getValue().getSup();
				// Note: using solution_inf or solution_sup alone sometimes fails 
				// because of floating point inaccuracies
				pcVar.solution=(pcVar.solution_inf + pcVar.solution_sup) / 2;
				
				pb.post(pb.eq(chocoVar, pcVar.solution));
				isSolvable = pb.solve();
				if (isSolvable == null) 
					isSolvable = Boolean.FALSE;
			}
			
				// compute solutions for integer variables
				Set<Entry<SymbolicInteger,IntDomainVar>> sym_intvar_mappings = symIntegerVar.entrySet();
				Iterator<Entry<SymbolicInteger,IntDomainVar>> i_int = sym_intvar_mappings.iterator();
				while(i_int.hasNext()) {
					Entry<SymbolicInteger,IntDomainVar> e =  i_int.next();
					//System.out.println("solution +"+ e.getValue().getVal());
					e.getKey().solution=e.getValue().getVal(); // not clear if we still need to carry this info
				}
			}
		}
	}
