//
// Copyright (C) 2007 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.bytecode.*;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemChoco;
import gov.nasa.jpf.util.InstructionFactoryFilter;


public class SymbolicInstructionFactory extends gov.nasa.jpf.jvm.bytecode.InstructionFactory {
	  @Override
	  public ALOAD aload(int localVarIndex) {
	    return new ALOAD(localVarIndex);
	  }


	  @Override
	  public ALOAD aload_0() {
	    return new ALOAD(0);
	  }

	  @Override
	  public ALOAD aload_1() {
	    return new ALOAD(1);
	  }

	  @Override
	  public ALOAD aload_2() {
	    return new ALOAD(2);
	  }

	  @Override
	  public ALOAD aload_3() {
	    return new ALOAD(3);
	  }

	  @Override
	  public IADD iadd() {
	    return new IADD();
	  }

	  @Override
	  public IAND iand() {
	    return new IAND();
	  }

	  @Override
	  public IINC iinc(int localVarIndex, int incConstant) {
		    return new IINC(localVarIndex, incConstant);
	  }

	  @Override
	  public ISUB isub() {
	    return new ISUB();
	  }

	  @Override
	  public IMUL imul() {
	    return new IMUL();
	  }

	  @Override
	  public INEG ineg() {
	    return new INEG();
	  }

	  @Override
	  public IFLE ifle(int targetPc) {
	    return new IFLE(targetPc);
	  }

	  @Override
	  public IFLT iflt(int targetPc) {
	    return new IFLT(targetPc);
	  }

	  @Override
	  public IFGE ifge(int targetPc) {
	    return new IFGE(targetPc);
	  }

	  @Override
	  public IFGT ifgt(int targetPc) {
	    return new IFGT(targetPc);
	  }

	  @Override
	  public IFEQ ifeq(int targetPc) {
	    return new IFEQ(targetPc);
	  }

	  @Override
	  public IFNE ifne(int targetPc) {
	    return new IFNE(targetPc);
	  }

	  @Override
	  public INVOKESTATIC invokestatic(String clsName, String methodName, String methodSignature) {
	    return new INVOKESTATIC(clsName, methodName, methodSignature);
	  }

	  @Override
	  public INVOKEVIRTUAL invokevirtual(String clsName, String methodName, String methodSignature) {
		    return new INVOKEVIRTUAL(clsName, methodName, methodSignature);
	  }

	  @Override
	  public INVOKESPECIAL invokespecial(String clsName, String methodName, String methodSignature) {
		    return new INVOKESPECIAL(clsName, methodName, methodSignature);
	  }

	  @Override
	  public IF_ICMPGE if_icmpge(int targetPc) {
		    return new IF_ICMPGE(targetPc);
	  }

	  @Override
	  public IF_ICMPGT if_icmpgt(int targetPc) {
		    return new IF_ICMPGT(targetPc);
	  }

	  @Override
	  public IF_ICMPLE if_icmple(int targetPc) {
		    return new IF_ICMPLE(targetPc);
	  }

	  @Override
	  public IF_ICMPLT if_icmplt(int targetPc) {
		    return new IF_ICMPLT(targetPc);
	  }

	  @Override
	  public IDIV idiv() {
	    return new IDIV();
	  }

	  @Override
	  public ISHL ishl() {
	    return new ISHL();
	  }

	  @Override
	  public ISHR ishr() {
	    return new ISHR();
	  }

	  @Override
	  public IUSHR iushr() {
	    return new IUSHR();
	  }

	  @Override
	  public IXOR ixor() {
	    return new IXOR();
	  }

	  @Override
	  public IOR ior() {
	    return new IOR();
	  }

	  @Override
	  public IREM irem() {
	    return new IREM();
	  }

	  @Override
	  public IF_ICMPEQ if_icmpeq(int targetPc) {
		    return new IF_ICMPEQ(targetPc);
	  }

	  @Override
	  public IF_ICMPNE if_icmpne(int targetPc) {
		    return new IF_ICMPNE(targetPc);
	  }


	  @Override
	  public FADD fadd() {
	    return new FADD();
	  }

	  @Override
	  public FDIV fdiv() {
	    return new FDIV();
	  }

	  @Override
	  public FMUL fmul() {
	    return new FMUL();
	  }

	  @Override
	  public FNEG fneg() {
	    return new FNEG();
	  }

	  @Override
	  public FREM frem() {
	    return new FREM();
	  }

	  @Override
	  public FSUB fsub() {
	    return new FSUB();
	  }

	  @Override
	  public FCMPG fcmpg() {
	    return new FCMPG();
	  }

	  @Override
	  public FCMPL fcmpl() {
		    return new FCMPL();
		  }

	  @Override
	  public DADD dadd() {
		    return new DADD();
		  }

	  @Override
	  public DCMPG dcmpg() {
		    return new DCMPG();
		  }

	  @Override
	  public DCMPL dcmpl() {
		    return new DCMPL();
		  }

	  @Override
	  public DDIV ddiv() {
		    return new DDIV();
		  }

	  @Override
	  public DMUL dmul() {
		    return new DMUL();
		  }

	  @Override
	  public DNEG dneg() {
		    return new DNEG();
		  }

	  @Override
	  public DREM drem() {
		    return new DREM();
		  }

	  @Override
	  public DSUB dsub() {
		    return new DSUB();
		  }

	  @Override
	  public LADD ladd() {
		    return new LADD();
		  }

	  @Override
	  public LAND land() {
		    return new LAND();
		  }

	  @Override
	  public LCMP lcmp() {
		    return new LCMP();
		  }

	  @Override
	  public LDIV ldiv() {
		    return new LDIV();
		  }

	  @Override
	  public LMUL lmul() {
		    return new LMUL();
		  }

	  @Override
	  public LNEG lneg() {
		    return new LNEG();
		  }

	  @Override
	  public LOR lor() {
		    return new LOR();
		  }

	  @Override
	  public LREM lrem() {
		    return new LREM();
		  }

	  @Override
	  public LSHL lshl() {
		    return new LSHL();
		  }

	  @Override
	  public LSHR lshr() {
		    return new LSHR();
		  }

	  @Override
	  public LSUB lsub() {
		    return new LSUB();
		  }

	  @Override
	  public LUSHR lushr() {
		    return new LUSHR();
		  }

	  @Override
	  public LXOR lxor() {
		    return new LXOR();
		  }

	  @Override
	  public I2D i2d() {
		    return new I2D();
		  }

	  @Override
	  public D2I d2i() {
		    return new D2I();
		  }

	  @Override
	  public D2L d2l() {
		    return new D2L();
		  }

	  @Override
	  public I2F i2f() {
		    return new I2F();
		  }

	  @Override
	  public L2D l2d() {
		    return new L2D();
		  }

	  @Override
	  public L2F l2f() {
		    return new L2F();
		  }

	  @Override
	  public F2L f2l() {
		    return new F2L();
		  }

	  @Override
	  public F2I f2i() {
		    return new F2I();
		  }

	  @Override
	  public LOOKUPSWITCH lookupswitch(int defaultTargetPc, int nEntries) {
		    return new LOOKUPSWITCH(defaultTargetPc, nEntries);
		  }

	  @Override
	  public TABLESWITCH tableswitch(int defaultTargetPc, int low, int high) {
		    return new TABLESWITCH(defaultTargetPc, low, high);
		  }

	  @Override
	  public D2F d2f() {
		    return new D2F();
		  }

	  @Override
	  public F2D f2d() {
		    return new F2D();
		  }

	  @Override
	  public I2B i2b() {
		    return new I2B();
		  }

	  @Override
	  public I2C i2c() {
		    return new I2C();
		  }

	  @Override
	  public I2S i2s() {
		    return new I2S();
		  }

	  @Override
	  public I2L i2l() {
		    return new I2L();
		  }

	  @Override
	  public L2I l2i() {
		    return new L2I();
		  }

	  @Override
	  public GETFIELD getfield(String fieldName, String clsName, String fieldDescriptor){
		    return new GETFIELD(fieldName, clsName, fieldDescriptor);
		  }
	  @Override
	  public GETSTATIC getstatic(String fieldName, String clsName, String fieldDescriptor){
		    return new GETSTATIC(fieldName, clsName, fieldDescriptor);
		  }

		//TODO: to review
        //From Fujitsu:

	  @Override
	  public NEW new_(String clsName) {
		    return new NEW(clsName);
		  }
	  @Override
	  public IFNONNULL ifnonnull(int targetPc) {
		    return new IFNONNULL(targetPc);
		  }
	  @Override
	  public IFNULL ifnull(int targetPc) {
		    return new IFNULL(targetPc);
		  }





	static public String[] dp;

	/* Symbolic String configuration */
	static public String[] string_dp;
	static public int stringTimeout;

	/*
	 * This is intended to serve as a catchall debug flag.
	 * If there's some debug printing/outputing, conditionally print using
	 * this flag.
	 */
	static public boolean debugMode;

	/*
	 * Concolic mode where we concrete execute for now
	 * only Math operations
	 */

	static public boolean concolicMode;
	static public boolean heuristicRandomMode;
	static public boolean heuristicPartitionMode;
	static public int MaxTries = 1;

//TODO: check
	InstructionFactoryFilter filter = new InstructionFactoryFilter(null, new String[] {/*"java.*",*/ "javax.*" },
			null, null);


	public  SymbolicInstructionFactory (Config conf){
		System.out.println("Running Symbolic PathFinder ...");

		dp = conf.getStringArray("symbolic.dp");
		if (dp == null) {
			dp = new String[1];
			dp[0] = "choco";
		}
		System.out.println("symbolic.dp="+dp[0]);

		stringTimeout = conf.getInt("symbolic.string_dp_timeout_ms");
		System.out.println("symbolic.string_dp_timeout_ms="+stringTimeout);

		string_dp = conf.getStringArray("symbolic.string_dp");
		if (string_dp == null) {
			string_dp = new String[1];
			string_dp[0] = "none";
		}
		System.out.println("symbolic.string_dp="+string_dp[0]);



		//Just checking if set, don't care about any values
		String[] dummy = conf.getStringArray("symbolic.debug");
		if (dummy != null) {
			debugMode = true;
		} else {
			debugMode = false;
		}

		String[] concolic  = conf.getStringArray("symbolic.concolic");
		if (concolic != null) {
			concolicMode = true;
			System.out.println("symbolic.concolic=true");
		} else {
			concolicMode = false;
		}

		String[] concolicMaxTries  = conf.getStringArray("symbolic.concolic.MAX_TRIES");
		if (concolicMaxTries != null) {
			MaxTries = Integer.parseInt(concolicMaxTries[0]);
			assert (MaxTries > 0);
			System.out.println("symbolic.concolic.MAX_TRIES=" + MaxTries);
		} else {
			MaxTries = 1;
		}

		String[] heuristicRandom  = conf.getStringArray("symbolic.heuristicRandom");
		if (heuristicRandom != null) {
			heuristicRandomMode = true;
			System.out.println("symbolic.heuristicRandom=true");
		} else {
			heuristicRandomMode = false;
		}

		String[] heuristicPartition  = conf.getStringArray("symbolic.heuristicPartition");
		if (heuristicPartition != null) {
			assert(! heuristicRandomMode);
			heuristicPartitionMode = true;
			System.out.println("symbolic.heuristicPartition=true");
		} else {
			heuristicPartitionMode = false;
		}

		if(dp[0].equalsIgnoreCase("choco") || dp[0].equalsIgnoreCase("debug") || dp[0].equalsIgnoreCase("compare") || dp == null) { // default is choco
		  ProblemChoco.timeBound = conf.getInt("symbolic.choco_time_bound", 30000);
		  System.out.println("symbolic.choco_time_bound="+ProblemChoco.timeBound);
		}
		String[] intmin, intmax, realmin, realmax, dontcare;
		intmin = conf.getStringArray("symbolic.minint");
		intmax = conf.getStringArray("symbolic.maxint");
		realmin = conf.getStringArray("symbolic.minreal");
		realmax = conf.getStringArray("symbolic.maxreal");
		dontcare = conf.getStringArray("symbolic.undefined");

		if (intmin != null && intmin[0] != null)
			MinMax.MININT = new Integer(intmin[0]);
		if (intmax != null && intmax[0] != null)
			MinMax.MAXINT = new Integer(intmax[0]);
		if (realmin != null && realmin[0] != null)
			MinMax.MINDOUBLE = new Double(realmin[0]);
		if (realmax != null && realmax[0] != null)
			MinMax.MAXDOUBLE = new Double(realmax[0]);
		if (dontcare != null && dontcare[0] != null) {
			SymbolicInteger.UNDEFINED = new Integer(dontcare[0]);
			SymbolicReal.UNDEFINED = new Double(dontcare[0]);
		}
		System.out.println("symbolic.minint="+MinMax.MININT);
		System.out.println("symbolic.maxint="+MinMax.MAXINT);
		System.out.println("symbolic.minreal="+MinMax.MINDOUBLE);
		System.out.println("symbolic.maxreal="+MinMax.MAXDOUBLE);
		System.out.println("symbolic.undefined="+SymbolicInteger.UNDEFINED);
		if((SymbolicInteger.UNDEFINED >= MinMax.MININT && SymbolicInteger.UNDEFINED <= MinMax.MAXINT) &&
			(SymbolicInteger.UNDEFINED >= MinMax.MINDOUBLE && SymbolicInteger.UNDEFINED <= MinMax.MAXDOUBLE))
			System.err.println("Warning: undefined value should be outside  min..max ranges");

	}


}
