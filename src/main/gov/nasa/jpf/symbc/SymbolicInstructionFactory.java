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
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.symbc.bytecode.*;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.numeric.SymbolicReal;
import gov.nasa.jpf.symbc.numeric.solvers.ProblemChoco;
import gov.nasa.jpf.util.InstructionFactoryFilter;


public class SymbolicInstructionFactory extends gov.nasa.jpf.jvm.bytecode.InstructionFactory {
	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ALOAD aload(int localVarIndex) {
	    return filter.isInstrumentedClass(ci) ? new ALOAD(localVarIndex) : (ALOAD) super.aload(localVarIndex);
	  }


	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ALOAD aload_0() {
	    return filter.isInstrumentedClass(ci) ? new ALOAD(0): super.aload_0();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ALOAD aload_1() {
	    return filter.isInstrumentedClass(ci) ? new ALOAD(1): super.aload_1();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ALOAD aload_2() {
	    return filter.isInstrumentedClass(ci) ? new ALOAD(2): super.aload_2();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ALOAD aload_3() {
	    return filter.isInstrumentedClass(ci) ? new ALOAD(3): super.aload_3();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IADD iadd() {
	    return filter.isInstrumentedClass(ci) ? new IADD(): super.iadd();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IAND iand() {
	    return filter.isInstrumentedClass(ci) ? new IAND(): super.iand() ;
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IINC iinc(int localVarIndex, int incConstant) {
		    return filter.isInstrumentedClass(ci) ? new IINC(localVarIndex, incConstant) :super.iinc(localVarIndex, incConstant);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ISUB isub() {
	    return filter.isInstrumentedClass(ci) ? new ISUB() : super.isub();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IMUL imul() {
	    return filter.isInstrumentedClass(ci) ? new IMUL() : super.imul();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.INEG ineg() {
	    return filter.isInstrumentedClass(ci) ? new INEG() : super.ineg();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFLE ifle(int targetPc) {
	    return filter.isInstrumentedClass(ci) ? new IFLE(targetPc) : super.ifle(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFLT iflt(int targetPc) {
	    return filter.isInstrumentedClass(ci) ? new IFLT(targetPc) : super.iflt(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFGE ifge(int targetPc) {
	    return filter.isInstrumentedClass(ci) ? new IFGE(targetPc): super.ifge(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFGT ifgt(int targetPc) {
	    return filter.isInstrumentedClass(ci) ? new IFGT(targetPc): super.ifgt(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFEQ ifeq(int targetPc) {
	    return filter.isInstrumentedClass(ci) ? new IFEQ(targetPc): super.ifeq(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFNE ifne(int targetPc) {
	    return filter.isInstrumentedClass(ci) ? new IFNE(targetPc): super.ifne(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.INVOKESTATIC invokestatic(String clsName, String methodName, String methodSignature) {
	    return filter.isInstrumentedClass(ci) ? new INVOKESTATIC(clsName, methodName, methodSignature): super.invokestatic(clsName, methodName, methodSignature)
	    		;
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.INVOKEVIRTUAL invokevirtual(String clsName, String methodName, String methodSignature) {
		    return filter.isInstrumentedClass(ci) ? new INVOKEVIRTUAL(clsName, methodName, methodSignature): super.invokevirtual(clsName, methodName, methodSignature);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.INVOKESPECIAL invokespecial(String clsName, String methodName, String methodSignature) {
		    return filter.isInstrumentedClass(ci) ? new INVOKESPECIAL(clsName, methodName, methodSignature): super.invokespecial(clsName, methodName, methodSignature);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IF_ICMPGE if_icmpge(int targetPc) {
		    return filter.isInstrumentedClass(ci) ? new IF_ICMPGE(targetPc): super.if_icmpge(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IF_ICMPGT if_icmpgt(int targetPc) {
		    return filter.isInstrumentedClass(ci) ? new IF_ICMPGT(targetPc): super.if_icmpgt(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IF_ICMPLE if_icmple(int targetPc) {
		    return filter.isInstrumentedClass(ci) ? new IF_ICMPLE(targetPc): super.if_icmple(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IF_ICMPLT if_icmplt(int targetPc) {
		    return filter.isInstrumentedClass(ci) ? new IF_ICMPLT(targetPc): super.if_icmplt(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IDIV idiv() {
	    return filter.isInstrumentedClass(ci) ? new IDIV(): super.idiv();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ISHL ishl() {
	    return filter.isInstrumentedClass(ci) ? new ISHL(): super.ishl();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.ISHR ishr() {
	    return filter.isInstrumentedClass(ci) ? new ISHR(): super.ishr();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IUSHR iushr() {
	    return filter.isInstrumentedClass(ci) ? new IUSHR(): super.iushr();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IXOR ixor() {
	    return filter.isInstrumentedClass(ci) ? new IXOR(): super.ixor();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IOR ior() {
	    return filter.isInstrumentedClass(ci) ? new IOR(): super.ior();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IREM irem() {
	    return filter.isInstrumentedClass(ci) ? new IREM(): super.irem();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IF_ICMPEQ if_icmpeq(int targetPc) {
		    return filter.isInstrumentedClass(ci) ? new IF_ICMPEQ(targetPc): super.if_icmpeq(targetPc);
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IF_ICMPNE if_icmpne(int targetPc) {
		    return filter.isInstrumentedClass(ci) ? new IF_ICMPNE(targetPc): super.if_icmpne(targetPc);
	  }


	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FADD fadd() {
	    return filter.isInstrumentedClass(ci) ? new FADD(): super.fadd();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FDIV fdiv() {
	    return filter.isInstrumentedClass(ci) ? new FDIV(): super.fdiv();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FMUL fmul() {
	    return filter.isInstrumentedClass(ci) ? new FMUL(): super.fmul();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FNEG fneg() {
	    return filter.isInstrumentedClass(ci) ? new FNEG(): super.fneg();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FREM frem() {
	    return filter.isInstrumentedClass(ci) ? new FREM(): super.frem();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FSUB fsub() {
	    return filter.isInstrumentedClass(ci) ? new FSUB(): super.fsub();
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FCMPG fcmpg() {
	    return filter.isInstrumentedClass(ci) ? new FCMPG(): super.fcmpg()
	    		;
	  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.FCMPL fcmpl() {
		    return filter.isInstrumentedClass(ci) ? new FCMPL(): super.fcmpl();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DADD dadd() {
		    return filter.isInstrumentedClass(ci) ? new DADD(): super.dadd();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DCMPG dcmpg() {
		    return filter.isInstrumentedClass(ci) ? new DCMPG(): super.dcmpg();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DCMPL dcmpl() {
		    return filter.isInstrumentedClass(ci) ? new DCMPL(): super.dcmpl();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DDIV ddiv() {
		    return filter.isInstrumentedClass(ci) ? new DDIV(): super.ddiv();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DMUL dmul() {
		    return filter.isInstrumentedClass(ci) ? new DMUL(): super.dmul();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DNEG dneg() {
		    return filter.isInstrumentedClass(ci) ? new DNEG(): super.dneg();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DREM drem() {
		    return filter.isInstrumentedClass(ci) ? new DREM(): super.drem();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.DSUB dsub() {
		    return filter.isInstrumentedClass(ci) ? new DSUB(): super.dsub();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LADD ladd() {
		    return filter.isInstrumentedClass(ci) ? new LADD(): super.ladd();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LAND land() {
		    return filter.isInstrumentedClass(ci) ? new LAND(): super.land();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LCMP lcmp() {
		    return filter.isInstrumentedClass(ci) ? new LCMP(): super.lcmp();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LDIV ldiv() {
		    return filter.isInstrumentedClass(ci) ? new LDIV(): super.ldiv();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LMUL lmul() {
		    return filter.isInstrumentedClass(ci) ? new LMUL(): super.lmul();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LNEG lneg() {
		    return filter.isInstrumentedClass(ci) ? new LNEG(): super.lneg();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LOR lor() {
		  return filter.isInstrumentedClass(ci) ? new LOR(): super.lor();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LREM lrem() {
		  return filter.isInstrumentedClass(ci) ? new LREM(): super.lrem();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LSHL lshl() {
		  return filter.isInstrumentedClass(ci) ? new LSHL(): super.lshl();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LSHR lshr() {
		  return filter.isInstrumentedClass(ci) ? new LSHR(): super.lshr();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LSUB lsub() {
		  return filter.isInstrumentedClass(ci) ? new LSUB(): super.lsub();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LUSHR lushr() {
		  return filter.isInstrumentedClass(ci) ? new LUSHR(): super.lushr();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LXOR lxor() {
		  return filter.isInstrumentedClass(ci) ? new LXOR(): super.lxor();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2D i2d() {
		  return filter.isInstrumentedClass(ci) ? new I2D(): super.i2d();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.D2I d2i() {
		  return filter.isInstrumentedClass(ci) ? new D2I(): super.d2i();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.D2L d2l() {
		  return filter.isInstrumentedClass(ci) ?  new D2L(): super.d2l();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2F i2f() {
		  return filter.isInstrumentedClass(ci) ?  new I2F(): super.i2f();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.L2D l2d() {
		  return filter.isInstrumentedClass(ci) ?  new L2D(): super.l2d();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.L2F l2f() {
		  return filter.isInstrumentedClass(ci) ?  new L2F(): super.l2f();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.F2L f2l() {
		  return filter.isInstrumentedClass(ci) ?  new F2L(): super.f2l();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.F2I f2i() {
		  return filter.isInstrumentedClass(ci) ?  new F2I(): super.f2i();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.LOOKUPSWITCH lookupswitch(int defaultTargetPc, int nEntries) {
		  return filter.isInstrumentedClass(ci) ?  new LOOKUPSWITCH(defaultTargetPc, nEntries): super.lookupswitch(defaultTargetPc, nEntries);
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.TABLESWITCH tableswitch(int defaultTargetPc, int low, int high) {
		  return filter.isInstrumentedClass(ci) ?  new TABLESWITCH(defaultTargetPc, low, high): super.tableswitch(defaultTargetPc, low, high);
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.D2F d2f() {
		  return filter.isInstrumentedClass(ci) ?  new D2F(): super.d2f();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.F2D f2d() {
		  return filter.isInstrumentedClass(ci) ?  new F2D(): super.f2d();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2B i2b() {
		  return filter.isInstrumentedClass(ci) ?  new I2B(): super.i2b();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2C i2c() {
		  return filter.isInstrumentedClass(ci) ?  new I2C(): super.i2c();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2S i2s() {
		  return filter.isInstrumentedClass(ci) ?  new I2S(): super.i2s();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2L i2l() {
		  return filter.isInstrumentedClass(ci) ?  new I2L(): super.i2l();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.L2I l2i() {
		  return filter.isInstrumentedClass(ci) ?  new L2I(): super.l2i();
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.GETFIELD getfield(String fieldName, String clsName, String fieldDescriptor){
		  return filter.isInstrumentedClass(ci) ?  new GETFIELD(fieldName, clsName, fieldDescriptor): super.getfield(fieldName, clsName, fieldDescriptor);
		  }
	  @Override
	  public gov.nasa.jpf.jvm.bytecode.GETSTATIC getstatic(String fieldName, String clsName, String fieldDescriptor){
		  return filter.isInstrumentedClass(ci) ?  new GETSTATIC(fieldName, clsName, fieldDescriptor): super.getstatic(fieldName, clsName, fieldDescriptor);
		  }

		//TODO: to review
        //From Fujitsu:

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.NEW new_(String clsName) {
		  return filter.isInstrumentedClass(ci) ?  new NEW(clsName): super.new_(clsName);
		  }
	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFNONNULL ifnonnull(int targetPc) {
		  return filter.isInstrumentedClass(ci) ?  new IFNONNULL(targetPc): super.ifnonnull(targetPc);
		  }
	  @Override
	  public gov.nasa.jpf.jvm.bytecode.IFNULL ifnull(int targetPc) {
		  return filter.isInstrumentedClass(ci) ?  new IFNULL(targetPc): super.ifnull(targetPc);
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

	ClassInfo ci;
	InstructionFactoryFilter filter;

	 @Override
	 public void setClassInfoContext(ClassInfo ci){
		    this.ci = ci;
	 }

	 public  SymbolicInstructionFactory (Config conf){

		System.out.println("Running Symbolic PathFinder ...");

		filter = new InstructionFactoryFilter(null, new String[] {/*"java.*",*/ "javax.*" },null, null);

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
