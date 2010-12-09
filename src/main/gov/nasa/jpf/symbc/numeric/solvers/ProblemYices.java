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

package gov.nasa.jpf.symbc.numeric.solvers;



import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;


import yices.*;

public class ProblemYices extends ProblemGeneral {
	YicesLite yices;
	int ctx;
	static YicesLite oldYices;
	static int oldCtx;

	public ProblemYices() {
		//reset the old context
		if(oldYices!=null)
			oldYices.yicesl_del_context(oldCtx);

		yices = new YicesLite();
		ctx = yices.yicesl_mk_context();
//		yices.yicesl_read(ctx,"(set-evidence! true)");
//		yices.yicesl_read(ctx,"(set-arith-only! true)");
		yices.yicesl_set_verbosity((short)0);
		//pb.setPrecision(1e-8);// need to check this
//		workingDir = System.getProperty("user.dir");
	}

	public String makeIntVar(String name, int min, int max) {
		yices.yicesl_read(ctx,"(define "+name+"::int)");
		yices.yicesl_read(ctx,"(assert (> "+ name + " " + min +"))");
		yices.yicesl_read(ctx,"(assert (< "+ name + " " + max +"))");
		return name;
	}

	public String makeRealVar(String name, double min, double max) {
		yices.yicesl_read(ctx,"(define "+name+"::real)");
		yices.yicesl_read(ctx,"(assert (> "+ name + " " + min +"))");
		yices.yicesl_read(ctx,"(assert (< "+ name + " " + max +"))");
		return name;
	}

	public Object eq(int value, Object exp){return "(= " + value + " " + (String)exp + ")";}
	public Object eq(Object exp, int value){return "(= " + (String)exp + " " + value + ")";}
	public Object eq(Object exp1, Object exp2){
		return "(= " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object eq(double value, Object exp){return "(= " + value + " " + (String)exp + ")";}
	public Object eq(Object exp, double value){return "(= " + (String)exp + " " + value + ")";}
	public Object neq(int value, Object exp){return "(/= " + value + " " + (String)exp + ")";}
	public Object neq(Object exp, int value){return "(/= " + (String)exp + " " + value + ")";}
	public Object neq(Object exp1, Object exp2){
		return "(/= " + (String)exp1 + " " + (String)exp2 + ")";

	}
	public Object neq(double value, Object exp){return "(/= " + value + " " + (String)exp + ")";}
	public Object neq(Object exp, double value){return "(/= " + (String)exp + " " + value + ")";}
	public Object leq(int value, Object exp){return "(<= " + value + " " + (String)exp + ")";}
	public Object leq(Object exp, int value){return "(<= " + (String)exp + " " + value + ")";}
	public Object leq(Object exp1, Object exp2){
		return "(<= " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object leq(double value, Object exp){return "(<= " + value + " " + (String)exp + ")";}
	public Object leq(Object exp, double value){return "(<= " + (String)exp + " " + value + ")";}
	public Object geq(int value, Object exp){return "(>= " + value + " " + (String)exp + ")";}
	public Object geq(Object exp, int value){return "(>= " + (String)exp + " " + value + ")";}
	public Object geq(Object exp1, Object exp2){
		return "(>= " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object geq(double value, Object exp){
		return "(>= " + value + " " + (String)exp + ")";
	}
	public Object geq(Object exp, double value){
		return "(>= " + (String)exp + " " + value + ")";
	}
	public Object lt(int value, Object exp){
		return "(< " + value + " " + (String)exp + ")";
	}
	public Object lt(Object exp, int value){
		return "(< " + (String)exp + " " + value + ")";
	}
	public Object lt(Object exp1, Object exp2){
		return "(< " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object lt(double value, Object exp){
		return "(< " + value + " " + (String)exp + ")";
	}
	public Object lt(Object exp, double value){
		return "(< " + (String)exp + " " + value + ")";
	}
	public Object gt(int value, Object exp){
		return "(> " + value + " " + (String)exp + ")";
	}
	public Object gt(Object exp, int value){
		return "(> " + (String)exp + " " + value + ")";
	}
	public Object gt(Object exp1, Object exp2){
		return "(> " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object gt(double value, Object exp){
		return "(> " + value + " " + (String)exp + ")";
	}
	public Object gt(Object exp, double value){
		return "(> " + (String)exp + " " + value + ")";
	}

	public Object plus(int value, Object exp) {
		return "(+ " + value + " " + (String)exp + ")";
	}
	public Object plus(Object exp, int value) {
		return "(+ " + (String)exp + " " + value + ")";
	}
	public Object plus(Object exp1, Object exp2) {
		return "(+ " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object plus(double value, Object exp) {
		return "(+ " + value + " " + (String)exp + ")";
	}
	public Object plus(Object exp, double value) {
		return "(+ " + (String)exp + " " + value + ")";
	}

	public Object minus(int value, Object exp) {
		return "(- " + value + " " + (String)exp + ")";
	}
	public Object minus(Object exp, int value) {
		return "(- " + (String)exp + " " + value + ")";
	}
	public Object minus(Object exp1, Object exp2) {
		return "(- " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object minus(double value, Object exp) {
		return "(- " + value + " " + (String)exp + ")";
	}
	public Object minus(Object exp, double value) {
		return "(- " + (String)exp + " " + value + ")";
	}
	public Object mult(int value, Object exp) {
		return "(* " + value + " " + (String)exp + ")";
	}
	public Object mult(Object exp, int value) {
		return "(* " + (String)exp + " " + value + ")";
	}
	public Object mult(Object exp1, Object exp2) {
		return "(* " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object mult(double value, Object exp) {
		return "(* " + value + " " + (String)exp + ")";
	}
	public Object mult(Object exp, double value) {
		return "(* " + (String)exp + " " + value + ")";
	}
	public Object div(int value, Object exp) {
		return "(/ " + value + " " + (String)exp + ")";
	}
	public Object div(Object exp, int value) {
		return "(/ " + (String)exp + " " + value + ")";
	}
	public Object div(Object exp1, Object exp2) {
		return "(/ " + (String)exp1 + " " + (String)exp2 + ")";
	}
	public Object div(double value, Object exp) {
		return "(/ " + value + " " + (String)exp + ")";
	}
	public Object div(Object exp, double value) {
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
	public Object mixed(Object exp1, Object exp2) { // TODO:check !!!
		return "(= " + (String)exp1 + " " + (String)exp2 + ")";
	}

	public double getRealValueInf(Object dpVar) {
//		return ((RealVar) dpVar).getValue().getInf();
//		throw new RuntimeException("# Error: Yices can not compute realValueInf!");
		//System.out.println("# Warning: Yices can not compute realValueInf! (used 0.0)");
		//return 0.0;
		return getRealValue(dpVar);
	}
	public double getRealValueSup(Object dpVar) {
//		return ((RealVar) dpVar).getValue().getSup();
//		throw new RuntimeException("# Error: Yices can not compute realValueSup!");
		System.out.println("# Warning: Yices can not compute realValueSup! (used 0.0)");
		return 0.0;
	}
	public double getRealValue(Object dpVar) {
//		return ((IntDomainVar) dpVar).getVal();
//		System.out.println("lookup variable "+(String)dpVar);
		String vname = (String) dpVar;

		int sat = yices.yicesl_inconsistent(ctx);
		if(sat == 0){
			//dump solution
//			System.out.println(System.getProperty("user.dir"));
			String workingDir = System.getProperty("user.dir");

			yices.yicesl_set_output_file(workingDir+"/yicesOutput/out.txt");
			yices.yicesl_read(ctx,"(set-evidence! true)");
			yices.yicesl_read(ctx, "(check)");
			yices.yicesl_read(ctx,"(set-evidence! false)");

			//read in solution and look up the value to return
			BufferedReader bufferedReader = null;
			try {
				bufferedReader =  new BufferedReader(new FileReader(new File(workingDir+"/yicesOutput/out.txt")));
				String new_line;
				String delims = "[ ]+";
				 while((new_line = bufferedReader.readLine()) != null) {
					  String[] tokens = new_line.split(delims);
					  if(tokens.length == 3){
						  if(tokens[1].compareTo(vname) == 0){
							  int value = Integer.parseInt(tokens[2].substring(0, tokens[2].length()-1));
//							  System.out.println(vname+" = "+value);
							  return value;
						  }
					  }
		  		 }
			} catch (FileNotFoundException ex) {
		        ex.printStackTrace();
		    } catch (IOException ex) {
		        ex.printStackTrace();
		    } finally {
		        //Close the BufferedWriter
		        try {
		            if (bufferedReader != null) {
		                bufferedReader.close();
		            }
		        } catch (IOException ex) {
		            ex.printStackTrace();
		        }
		    }
		}
		//throw new RuntimeException("# Error: Yices didn't find real solution for variable "+vname);
		return 0.0;
	}
	static java.io.File f;
	static java.io.FileReader fr;


	public int getIntValue(Object dpVar) {

		String vname = (String) dpVar;

		int sat = yices.yicesl_inconsistent(ctx);

		if(sat == 0){
			//dump solution

			String workingDir = System.getProperty("user.dir");

			yices.yicesl_set_output_file(workingDir+"/yicesOutput/out.txt");
			yices.yicesl_read(ctx,"(set-evidence! true)");
			yices.yicesl_read(ctx, "(check)");
			yices.yicesl_read(ctx,"(set-evidence! false)");

			//read in solution and look up the value to return
			BufferedReader bufferedReader = null;

			try {

				f = new File(workingDir+"/yicesOutput/out.txt");
				fr = new FileReader(f);

				bufferedReader =  new BufferedReader(fr);//=new FileReader(f));//new File(workingDir+"/yicesOutput/out.txt")));//fr);
				String new_line;
				String delims = "[ ]+";

				while((new_line = bufferedReader.readLine()) != null) {

					  String[] tokens = new_line.split(delims);
					  for (int i =1; i < tokens.length; i=i+3) {

					  //if(tokens.length == 3){
						  if(tokens[i].compareTo(vname) == 0){
							  int value = Integer.parseInt(tokens[i+1].substring(0, tokens[i+1].length()-1));
//							  System.out.println(vname+" = "+value);
							  bufferedReader.close();
							  fr.close();
							  f = null;
							  fr = null;
							  return value;
						  }
					  }
				 }
				 bufferedReader.close();
				 fr.close();
				 f = null;
				 fr = null;


			} catch (Exception ex) {
		        ex.printStackTrace();
		    }
		}
		throw new RuntimeException("# Error: Yices didn't find int solution for variable "+vname);
	}

	public Boolean solve() {
//        pb.getSolver().setTimeLimit(30000);
//		yices.yicesl_read(ctx,"(dump-context)");
		int sat = yices.yicesl_inconsistent(ctx);

//		if(sat == 0){
//			yices.yicesl_read(ctx,"(set-evidence! true)");
//			yices.yicesl_read(ctx, "(check)");
//			yices.yicesl_read(ctx,"(set-evidence! false)");
//		}

//		yices.yicesl_del_context(ctx);
		oldYices = yices;
		oldCtx = ctx;
		return sat == 0 ? true : false;
	}
	public void post(Object constraint) {
		yices.yicesl_read(ctx,"(assert " + (String)constraint + ")");
	}



	public Object and(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise AND");
	}

	public Object and(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise AND");
	}

	public Object and(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise AND");
	}

	@Override
	public
	Object or(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise OR");
	}

	@Override
	public
	Object or(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise OR");
	}

	@Override
	public
	Object or(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise OR");
	}

	@Override
	public
	Object shiftL(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftL");
	}

	@Override
	public
	Object shiftL(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftL");
	}

	@Override
	public
	Object shiftR(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftR");
	}

	@Override
	public
	Object shiftR(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftR");
	}

	@Override
	public
	Object xor(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise XOR");
	}

	@Override
	public
	Object xor(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise XOR");
	}

	@Override
	public
	Object xor(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise XOR");
	}

	@Override
	public Object shiftL(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise shifL");
	}

	@Override
	public Object shiftR(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise shifR");
	}

	@Override
	public Object shiftUR(int value, Object exp) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftUR");
	}

	@Override
	public Object shiftUR(Object exp, int value) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftUR");
	}

	@Override
	public Object shiftUR(Object exp1, Object exp2) {
		throw new RuntimeException("## Error Yices does not support bitwise shiftUR");
	}

	@Override
	public void postLogicalOR(Object[] constraints) {
		assert(constraints != null && constraints.length >=1);
		String orResult = "";
		for (int i = 0; i<constraints.length; i++) {
			orResult += (String)constraints[i] + " ";
		}
		orResult = "(or " + orResult+ ")";
		post(orResult);
	}

}
