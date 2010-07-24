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

//import choco.Problem;
import choco.integer.*;
import choco.integer.var.IntTerm;
import choco.integer.var.IntTerm.*;
import choco.real.*;
import choco.real.constraint.MixedEqXY;

public class ProblemChoco extends ProblemGeneral {
	RealProblem pb;
	public static int timeBound;// = 30000;
	public ProblemChoco() {
		pb = new RealProblem();
		//pb.setPrecision(1e-8);// need to check this
	}

	IntDomainVar makeIntVar(String name, int min, int max) {
		return pb.makeBoundIntVar(name,min,max);
	}

	RealVar makeRealVar(String name, double min, double max) {
		return pb.makeRealVar(name,min,max);
	}

	Object eq(int value, Object exp){return pb.eq(value, (IntExp)exp);}
	Object eq(Object exp, int value){return pb.eq((IntExp) exp, value);}
	Object eq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.eq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.eq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object eq(double value, Object exp){return pb.eq(value, (RealExp) exp);}
	Object eq(Object exp, double value){return pb.eq(value, (RealExp) exp);}
	Object neq(int value, Object exp){return pb.neq(value, (IntExp) exp);}
	Object neq(Object exp, int value){return pb.neq(value, (IntExp) exp);}
	Object neq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.neq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.neq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object neq(double value, Object exp){return pb.neq(value, (RealExp) exp);}
	Object neq(Object exp, double value){return pb.neq(value, (RealExp) exp);}
	Object leq(int value, Object exp){return pb.leq(value,(IntExp)exp);}
	Object leq(Object exp, int value){return pb.leq((IntExp)exp,value);}
	Object leq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.leq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.leq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object leq(double value, Object exp){return pb.leq(value,(RealExp)exp);}
	Object leq(Object exp, double value){return pb.leq((RealExp)exp, value);}
	Object geq(int value, Object exp){return pb.geq(value, (IntExp)exp);}
	Object geq(Object exp, int value){return pb.geq((IntExp)exp,value);}
	Object geq(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.geq((IntExp) exp1,(IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.geq((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object geq(double value, Object exp){
		return pb.geq(value, (RealExp) exp);
	}
	Object geq(Object exp, double value){
		return pb.geq((RealExp) exp, value);
	}
	Object lt(int value, Object exp){
		return pb.lt(value, (IntExp) exp);
	}
	Object lt(Object exp, int value){
		return pb.lt((IntExp) exp,value);
	}
	Object lt(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.lt((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.lt((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object lt(double value, Object exp){
		return pb.lt(value,(RealExp) exp);
	}
	Object lt(Object exp, double value){
		return pb.lt((RealExp) exp,value);
	}
	Object gt(int value, Object exp){
		return pb.gt(value,(IntExp) exp);
	}
	Object gt(Object exp, int value){
		return pb.gt((IntExp) exp,value);
	}
	Object gt(Object exp1, Object exp2){
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.gt((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.gt((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object gt(double value, Object exp){
		return pb.gt(value,(RealExp) exp);
	}
	Object gt(Object exp, double value){
		return pb.gt((RealExp) exp, value);
	}

	Object plus(int value, Object exp) {
		return pb.plus(value,(IntExp) exp);
	}
	Object plus(Object exp, int value) {
		return pb.plus((IntExp) exp, value);
	}
	Object plus(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.plus((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.plus((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object plus(double value, Object exp) {
		return pb.plus(pb.cst(value),(RealExp) exp);
	}
	Object plus(Object exp, double value) {
		return pb.plus((RealExp) exp, pb.cst(value));
	}

	Object minus(int value, Object exp) {
		return pb.minus(value, (IntExp) exp);
	}
	Object minus(Object exp, int value) {
		return pb.minus((IntExp) exp, value);
	}
	Object minus(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			return pb.minus((IntExp) exp1, (IntExp) exp2);
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.minus((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object minus(double value, Object exp) {
		return pb.minus(pb.cst(value), (RealExp) exp);
	}
	Object minus(Object exp, double value) {
		return pb.minus((RealExp) exp, pb.cst(value));
	}
	Object mult(int value, Object exp) {
		if (exp instanceof IntVar)
			return pb.mult(value, (IntExp) exp);
		else if (exp instanceof IntTerm) {
			// distribute value over exp
			//return pb.mult(value, (IntExp) exp);
			IntTerm it= (IntTerm) exp;
        	IntTerm constant= new IntTerm(0);
        	constant.setConstant(value * it.getConstant());
        	IntExp sum = constant;
        	for (int i = 0; i < it.getSize(); i++) {
        		IntTerm newterm= new IntTerm(1);
        		newterm.setCoefficient(i, it.getCoefficient(i)*value);
        		newterm.setVariable(i, it.getVariable(i));
        		sum= (IntExp) pb.plus(sum, newterm);
        	}
        	return sum;
		}
		else
			throw new RuntimeException("## Error Choco");
	}
	Object mult(Object exp, int value) {
		if (exp instanceof IntVar)
			return pb.mult(value, (IntExp) exp);
		else if (exp instanceof IntTerm) {
			// distribute value over exp
			//return pb.mult(value, (IntExp) exp);
			IntTerm it= (IntTerm) exp;
    		IntTerm constant= new IntTerm(0);
    		constant.setConstant(value * it.getConstant());
    		IntExp sum = constant;
    		for (int i = 0; i < it.getSize(); i++) {
    			IntTerm newterm= new IntTerm(1);
    			newterm.setCoefficient(i, it.getCoefficient(i)*value);
    			newterm.setVariable(i, it.getVariable(i));
    			sum= (IntExp) pb.plus(sum, newterm);
    		}
    		return sum;
		}
		else
			throw new RuntimeException("## Error Choco");
	}
	Object mult(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			throw new RuntimeException("## Error Choco: non-lin int constraint");
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.mult((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object mult(double value, Object exp) {
		return pb.mult(pb.cst(value), (RealExp) exp);
	}
	Object mult(Object exp, double value) {
		return pb.mult((RealExp) exp, pb.cst(value));
	}
	Object div(int value, Object exp) {
		throw new RuntimeException("## Error Choco: non-lin int constraint");
	}
	Object div(Object exp, int value) {
		throw new RuntimeException("## Error Choco: non-lin int constraint");
	}
	Object div(Object exp1, Object exp2) {
		if (exp1 instanceof IntExp && exp2 instanceof IntExp )
			throw new RuntimeException("## Error Choco: non-lin int constraint");
		else if (exp1 instanceof RealExp && exp2 instanceof RealExp)
			return pb.div((RealExp) exp1,(RealExp) exp2);
		else
			throw new RuntimeException("## Error Choco");
	}
	Object div(double value, Object exp) {
		return pb.div(pb.cst(value), (RealExp) exp);
	}
	Object div(Object exp, double value) {
		return pb.div((RealExp) exp,value);
	}
	Object sin(Object exp) {
		return pb.sin((RealExp) exp);
	}
	Object cos(Object exp) {
		return pb.cos((RealExp) exp);
	}

	Object power(Object exp, double value) {
		return pb.power((RealExp) exp, (int)value);
	}
	Object mixed(Object exp1, Object exp2) { // TODO:check !!!

		if (exp1 instanceof RealVar && exp2 instanceof IntVar)
			return new MixedEqXY((RealVar)exp1,(IntDomainVar)exp2);
		else
			throw new RuntimeException("## Error Choco: mixed");
	}

	double getRealValueInf(Object dpVar) {
		return ((RealVar) dpVar).getValue().getInf();
	}
	double getRealValueSup(Object dpVar) {
		return ((RealVar) dpVar).getValue().getSup();
	}
	double getRealValue(Object dpVar) {
		throw new RuntimeException("# Error: Choco can not compute real solution!");
	}
	int getIntValue(Object dpVar) {
		return ((IntDomainVar) dpVar).getVal();
	}

	Boolean solve() {
        pb.getSolver().setTimeLimit(ProblemChoco.timeBound);
		return pb.solve();
	}
	void post(Object constraint) {
		pb.post((choco.Constraint)constraint);
	}

	Object and(int value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise AND");
	}

	Object and(Object exp, int value) {
		throw new RuntimeException("## Error Choco does not support bitwise AND");
	}

	Object and(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise AND");
	}

	@Override
	Object or(int value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise OR");
	}

	@Override
	Object or(Object exp, int value) {
		throw new RuntimeException("## Error Choco does not support bitwise OR");
	}

	
	Object or(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise OR");
	}

	
	Object shiftL(int value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object shiftL(Object exp, int value) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object shiftR(int value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object shiftR(Object exp, int value) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object xor(int value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise XOR");
	}

	Object xor(Object exp, int value) {
		throw new RuntimeException("## Error Choco does not support bitwise XOR");
	}

	Object xor(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise XOR");
	}

	Object shiftL(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object shiftR(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object shiftUR(int value, Object exp) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
		
	}

	Object shiftUR(Object exp, int value) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}

	Object shiftUR(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Choco does not support bitwise SHIFT");
	}
	
}
