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

abstract class ProblemGeneral{
	abstract Object makeIntVar(String name, int min, int max);
	abstract Object makeRealVar(String name, double min, double max);

	abstract Object eq(int value, Object exp) ;
	abstract Object eq(Object exp, int value) ;
	abstract Object eq(Object exp1, Object exp2) ;
	abstract Object eq(double value, Object exp) ;
	abstract Object eq(Object exp, double value) ;
	abstract Object neq(int value, Object exp) ;
	abstract Object neq(Object exp, int value) ;
	abstract Object neq(Object exp1, Object exp2) ;
	abstract Object neq(double value, Object exp) ;
	abstract Object neq(Object exp, double value) ;
	abstract Object leq(int value, Object exp) ;
	abstract Object leq(Object exp, int value) ;
	abstract Object leq(Object exp1, Object exp2) ;
	abstract Object leq(double value, Object exp) ;
	abstract Object leq(Object exp, double value) ;
	abstract Object geq(int value, Object exp) ;
	abstract Object geq(Object exp, int value) ;
	abstract Object geq(Object exp1, Object exp2) ;
	abstract Object geq(double value, Object exp) ;
	abstract Object geq(Object exp, double value) ;
	abstract Object lt(int value, Object exp) ;
	abstract Object lt(Object exp, int value) ;
	abstract Object lt(Object exp1, Object exp2) ;
	abstract Object lt(double value, Object exp) ;
	abstract Object lt(Object exp, double value) ;
	abstract Object gt(int value, Object exp) ;
	abstract Object gt(Object exp, int value) ;
	abstract Object gt(Object exp1, Object exp2) ;
	abstract Object gt(double value, Object exp) ;
	abstract Object gt(Object exp, double value) ;

	abstract Object plus(int value, Object exp) ;
	abstract Object plus(Object exp, int value) ;
	abstract Object plus(Object exp1, Object exp2) ;
	abstract Object plus(double value, Object exp) ;
	abstract Object plus(Object exp, double value) ;
	abstract Object minus(int value, Object exp) ;
	abstract Object minus(Object exp, int value) ;
	abstract Object minus(Object exp1, Object exp2) ;
	abstract Object minus(double value, Object exp) ;
	abstract Object minus(Object exp, double value) ;
	abstract Object mult(int value, Object exp) ;
	abstract Object mult(Object exp, int value) ;
	abstract Object mult(Object exp1, Object exp2) ;
	abstract Object mult(double value, Object exp) ;
	abstract Object mult(Object exp, double value) ;
	abstract Object div(int value, Object exp) ;
	abstract Object div(Object exp, int value) ;
	abstract Object div(Object exp1, Object exp2) ;
	abstract Object div(double value, Object exp) ;
	abstract Object div(Object exp, double value) ;


	Object sin(Object exp) {
		throw new RuntimeException("## Error: Math.sin not supported");
	}
	Object cos(Object exp) {
		throw new RuntimeException("## Error: Math.cos not supported");
	}

	Object round(Object exp) {
		throw new RuntimeException("## Error: Math.round not supported");
	}
	Object exp(Object exp) {
		throw new RuntimeException("## Error: Math.exp not supported");
	}
	Object asin(Object exp) {
		throw new RuntimeException("## Error: Math.asin not supported");

	}
	Object acos(Object exp) {
		throw new RuntimeException("## Error: Math.acos not supported");

	}
	Object atan(Object exp) {
		throw new RuntimeException("## Error: Math.atan not supported");

	}
	Object log(Object exp) {
		throw new RuntimeException("## Error: Math.log not supported");

	}
	Object tan(Object exp) {
		throw new RuntimeException("## Error: Math.tan not supported");

	}
	Object sqrt(Object exp) {
		throw new RuntimeException("## Error: Math.sqrt not supported");

	}
	Object power(Object exp1, Object exp2) {
		throw new RuntimeException("## Error: Math.power not supported");
	}
	Object power(Object exp1, double exp2) {
		throw new RuntimeException("## Error: Math.power not supported");
	}
	Object power(double exp1, Object exp2) {
		throw new RuntimeException("## Error: Math.power not supported");
	}

	Object atan2(Object exp1, Object exp2) {
		throw new RuntimeException("## Error: Math.atan2 not supported");
	}
	Object atan2(Object exp1, double exp2) {
		throw new RuntimeException("## Error: Math.atan2 not supported");
	}
	Object atan2(double exp1, Object exp2) {
		throw new RuntimeException("## Error: Math.atan2 not supported");
	}

	abstract Object mixed(Object exp1, Object exp2);

	abstract Boolean solve();

	abstract double getRealValueInf(Object dpvar);
	abstract double getRealValueSup(Object dpVar);
	abstract double getRealValue(Object dpVar);
	abstract int getIntValue(Object dpVar);

	abstract void post(Object constraint);

}
