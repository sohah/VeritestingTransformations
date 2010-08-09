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

// author Pingyu Zhang pzhang@cse.unl.edu

package gov.nasa.jpf.symbc.numeric;

import yices.*;

public class ProblemYices extends ProblemGeneral {
	YicesLite yices;
	int ctx;
	public ProblemYices() {
		yices = new YicesLite();
		ctx = yices.yicesl_mk_context();
//		yices.yicesl_read(ctx,"(set-evidence! true)");
//		yices.yicesl_read(ctx,"(set-arith-only! true)");
		yices.yicesl_set_verbosity((short)0);
		//pb.setPrecision(1e-8);// need to check this
	}

	String makeIntVar(String name, int min, int max) {
		yices.yicesl_read(ctx,"(define "+name+"::int)");
//		yices.yicesl_read(ctx,"(assert (> "+ name + " " + min +"))");
//		yices.yicesl_read(ctx,"(assert (< "+ name + " " + max +"))");
		return name;
	}

	String makeRealVar(String name, double min, double max) {
		yices.yicesl_read(ctx,"(define "+name+"::real)");
//		yices.yicesl_read(ctx,"(assert (> "+ name + " " + min +"))");
//		yices.yicesl_read(ctx,"(assert (< "+ name + " " + max +"))");
		return name;
	}

	Object eq(int value, Object exp){return "(= " + value + " " + (String)exp + ")";}
	Object eq(Object exp, int value){return "(= " + (String)exp + " " + value + ")";}
	Object eq(Object exp1, Object exp2){
		return "(= " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object eq(double value, Object exp){return "(= " + value + " " + (String)exp + ")";}
	Object eq(Object exp, double value){return "(= " + (String)exp + " " + value + ")";}
	Object neq(int value, Object exp){return "(/= " + value + " " + (String)exp + ")";}
	Object neq(Object exp, int value){return "(/= " + (String)exp + " " + value + ")";}
	Object neq(Object exp1, Object exp2){
		return "(/= " + (String)exp1 + " " + (String)exp2 + ")";

	}
	Object neq(double value, Object exp){return "(/= " + value + " " + (String)exp + ")";}
	Object neq(Object exp, double value){return "(/= " + (String)exp + " " + value + ")";}
	Object leq(int value, Object exp){return "(<= " + value + " " + (String)exp + ")";}
	Object leq(Object exp, int value){return "(<= " + (String)exp + " " + value + ")";}
	Object leq(Object exp1, Object exp2){
		return "(<= " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object leq(double value, Object exp){return "(<= " + value + " " + (String)exp + ")";}
	Object leq(Object exp, double value){return "(<= " + (String)exp + " " + value + ")";}
	Object geq(int value, Object exp){return "(>= " + value + " " + (String)exp + ")";}
	Object geq(Object exp, int value){return "(>= " + (String)exp + " " + value + ")";}
	Object geq(Object exp1, Object exp2){
		return "(>= " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object geq(double value, Object exp){
		return "(>= " + value + " " + (String)exp + ")";
	}
	Object geq(Object exp, double value){
		return "(>= " + (String)exp + " " + value + ")";
	}
	Object lt(int value, Object exp){
		return "(< " + value + " " + (String)exp + ")";
	}
	Object lt(Object exp, int value){
		return "(< " + (String)exp + " " + value + ")";
	}
	Object lt(Object exp1, Object exp2){
		return "(< " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object lt(double value, Object exp){
		return "(< " + value + " " + (String)exp + ")";
	}
	Object lt(Object exp, double value){
		return "(< " + (String)exp + " " + value + ")";
	}
	Object gt(int value, Object exp){
		return "(> " + value + " " + (String)exp + ")";
	}
	Object gt(Object exp, int value){
		return "(> " + (String)exp + " " + value + ")";
	}
	Object gt(Object exp1, Object exp2){
		return "(> " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object gt(double value, Object exp){
		return "(> " + value + " " + (String)exp + ")";
	}
	Object gt(Object exp, double value){
		return "(> " + (String)exp + " " + value + ")";
	}

	Object plus(int value, Object exp) {
		return "(+ " + value + " " + (String)exp + ")";
	}
	Object plus(Object exp, int value) {
		return "(+ " + (String)exp + " " + value + ")";
	}
	Object plus(Object exp1, Object exp2) {
		return "(+ " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object plus(double value, Object exp) {
		return "(+ " + value + " " + (String)exp + ")";
	}
	Object plus(Object exp, double value) {
		return "(+ " + (String)exp + " " + value + ")";
	}

	Object minus(int value, Object exp) {
		return "(- " + value + " " + (String)exp + ")";
	}
	Object minus(Object exp, int value) {
		return "(- " + (String)exp + " " + value + ")";
	}
	Object minus(Object exp1, Object exp2) {
		return "(- " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object minus(double value, Object exp) {
		return "(- " + value + " " + (String)exp + ")";
	}
	Object minus(Object exp, double value) {
		return "(- " + (String)exp + " " + value + ")";
	}
	Object mult(int value, Object exp) {
		return "(* " + value + " " + (String)exp + ")";
	}
	Object mult(Object exp, int value) {
		return "(* " + (String)exp + " " + value + ")";
	}
	Object mult(Object exp1, Object exp2) {
		return "(* " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object mult(double value, Object exp) {
		return "(* " + value + " " + (String)exp + ")";
	}
	Object mult(Object exp, double value) {
		return "(* " + (String)exp + " " + value + ")";
	}
	Object div(int value, Object exp) {
		return "(/ " + value + " " + (String)exp + ")";
	}
	Object div(Object exp, int value) {
		return "(/ " + (String)exp + " " + value + ")";
	}
	Object div(Object exp1, Object exp2) {
		return "(/ " + (String)exp1 + " " + (String)exp2 + ")";
	}
	Object div(double value, Object exp) {
		return "(/ " + value + " " + (String)exp + ")";
	}
	Object div(Object exp, double value) {
		return "(/ " + (String)exp + " " + value + ")";
	}
//	Object sin(Object exp) {
//		return pb.sin((RealExp) exp);
//	}
//	Object cos(Object exp) {
//		return pb.cos((RealExp) exp);
//	}
//
//	Object power(Object exp, double value) {
//		return pb.power((RealExp) exp, (int)value);
//	}
	Object mixed(Object exp1, Object exp2) { // TODO:check !!!
		return "(= " + (String)exp1 + " " + (String)exp2 + ")";
	}

	double getRealValueInf(Object dpVar) {
//		return ((RealVar) dpVar).getValue().getInf();
		throw new RuntimeException("# Error: Yices can not compute realValueInf!");
	}
	double getRealValueSup(Object dpVar) {
//		return ((RealVar) dpVar).getValue().getSup();
		throw new RuntimeException("# Error: Yices can not compute realValueSup!");
	}
	double getRealValue(Object dpVar) {
//		throw new RuntimeException("# Error: Choco can not compute real solution!");
		throw new RuntimeException("# Error: Yices can not compute real solution!");
	}
	int getIntValue(Object dpVar) {
		return 0;
		//return yices.yicesl_read(ctx, (String) dpVar);//((IntDomainVar) dpVar).getVal();
		//throw new RuntimeException("# Error: Yices can not compute int solution!");
	}

	Boolean solve() {
//      pb.getSolver().setTimeLimit(30000);
//		yices.yicesl_read(ctx,"(dump-context)");
//		yices.yicesl_read(ctx,"(check)");
		int sat = yices.yicesl_inconsistent(ctx);
//		yices.yicesl_read(ctx,"(dump-context)");
		yices.yicesl_del_context(ctx);
//		System.out.println("Yices Solver Returns SAT="+sat);
		return sat == 0 ? true : false;
	}
	void post(Object constraint) {
		yices.yicesl_read(ctx,"(assert " + (String)constraint + ")");
	}

	Object and(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise AND");
	}

	Object and(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise AND");
	}

	Object and(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise AND");
	}

	@Override
	Object or(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise OR");
	}

	@Override
	Object or(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise OR");
	}

	@Override
	Object or(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise OR");
	}

	@Override
	Object shiftL(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftL");
	}

	@Override
	Object shiftL(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftL");
	}

	@Override
	Object shiftR(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftR");
	}

	@Override
	Object shiftR(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftR");
	}

	@Override
	Object xor(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise XOR");
	}

	@Override
	Object xor(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise XOR");
	}

	@Override
	Object xor(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise XOR");
	}

	@Override
	Object shiftL(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftL");
	}

	@Override
	Object shiftR(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftR");
	}

	@Override
	Object shiftUR(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftUR");
	}

	@Override
	Object shiftUR(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftUR");
	}

	@Override
	Object shiftUR(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("## Error Yices does not support bitwise ShiftUR");
	}


}
