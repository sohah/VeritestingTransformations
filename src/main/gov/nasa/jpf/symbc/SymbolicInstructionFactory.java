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
	  public ALOAD aload_0() {
	    return (ALOAD) (filter.isInstrumentedClass(ci) ? new ALOAD(0): super.aload_0());
	  }

	  @Override
	  public ALOAD aload_1() {
	    return (ALOAD) (filter.isInstrumentedClass(ci) ? new ALOAD(1): super.aload_1());
	  }

	  @Override
	  public ALOAD aload_2() {
	    return (ALOAD) (filter.isInstrumentedClass(ci) ? new ALOAD(2): super.aload_2());
	  }

	  @Override
	  public ALOAD aload_3() {
	    return (ALOAD) (filter.isInstrumentedClass(ci) ? new ALOAD(3): super.aload_3());
	  }

	  @Override
	  public IADD iadd() {
	    return (IADD) (filter.isInstrumentedClass(ci) ? new IADD(): super.iadd());
	  }

	  @Override
	  public IAND iand() {
	    return (IAND) (filter.isInstrumentedClass(ci) ? new IAND(): super.iand()) ;
	  }

	  @Override
	  public IINC iinc(int localVarIndex, int incConstant) {
		    return (IINC) (filter.isInstrumentedClass(ci) ? new IINC(localVarIndex, incConstant) :super.iinc(localVarIndex, incConstant));
	  }

	  @Override
	  public ISUB isub() {
	    return (ISUB) (filter.isInstrumentedClass(ci) ? new ISUB() : super.isub());
	  }

	  @Override
	  public IMUL imul() {
	    return (IMUL) (filter.isInstrumentedClass(ci) ? new IMUL() : super.imul());
	  }

	  @Override
	  public INEG ineg() {
	    return (INEG) (filter.isInstrumentedClass(ci) ? new INEG() : super.ineg());
	  }

	  @Override
	  public IFLE ifle(int targetPc) {
	    return (IFLE) (filter.isInstrumentedClass(ci) ? new IFLE(targetPc) : super.ifle(targetPc));
	  }

	  @Override
	  public IFLT iflt(int targetPc) {
	    return (IFLT) (filter.isInstrumentedClass(ci) ? new IFLT(targetPc) : super.iflt(targetPc));
	  }

	  @Override
	  public IFGE ifge(int targetPc) {
	    return (IFGE) (filter.isInstrumentedClass(ci) ? new IFGE(targetPc): super.ifge(targetPc));
	  }

	  @Override
	  public IFGT ifgt(int targetPc) {
	    return (IFGT) (filter.isInstrumentedClass(ci) ? new IFGT(targetPc): super.ifgt(targetPc));
	  }

	  @Override
	  public IFEQ ifeq(int targetPc) {
	    return (IFEQ) (filter.isInstrumentedClass(ci) ? new IFEQ(targetPc): super.ifeq(targetPc));
	  }

	  @Override
	  public IFNE ifne(int targetPc) {
	    return (IFNE) (filter.isInstrumentedClass(ci) ? new IFNE(targetPc): super.ifne(targetPc));
	  }

	  @Override
	  public INVOKESTATIC invokestatic(String clsName, String methodName, String methodSignature) {
	    return (INVOKESTATIC) (filter.isInstrumentedClass(ci) ? new INVOKESTATIC(clsName, methodName, methodSignature): super.invokestatic(clsName, methodName, methodSignature))
	    		;
	  }

	  @Override
	  public INVOKEVIRTUAL invokevirtual(String clsName, String methodName, String methodSignature) {
		    return (INVOKEVIRTUAL) (filter.isInstrumentedClass(ci) ? new INVOKEVIRTUAL(clsName, methodName, methodSignature): super.invokevirtual(clsName, methodName, methodSignature));
	  }

	  @Override
	  public INVOKESPECIAL invokespecial(String clsName, String methodName, String methodSignature) {
		    return (INVOKESPECIAL) (filter.isInstrumentedClass(ci) ? new INVOKESPECIAL(clsName, methodName, methodSignature): super.invokespecial(clsName, methodName, methodSignature));
	  }

	  @Override
	  public IF_ICMPGE if_icmpge(int targetPc) {
		    return (IF_ICMPGE) (filter.isInstrumentedClass(ci) ? new IF_ICMPGE(targetPc): super.if_icmpge(targetPc));
	  }

	  @Override
	  public IF_ICMPGT if_icmpgt(int targetPc) {
		    return (IF_ICMPGT) (filter.isInstrumentedClass(ci) ? new IF_ICMPGT(targetPc): super.if_icmpgt(targetPc));
	  }

	  @Override
	  public IF_ICMPLE if_icmple(int targetPc) {
		    return (IF_ICMPLE) (filter.isInstrumentedClass(ci) ? new IF_ICMPLE(targetPc): super.if_icmple(targetPc));
	  }

	  @Override
	  public IF_ICMPLT if_icmplt(int targetPc) {
		    return (IF_ICMPLT) (filter.isInstrumentedClass(ci) ? new IF_ICMPLT(targetPc): super.if_icmplt(targetPc));
	  }

	  @Override
	  public IDIV idiv() {
	    return (IDIV) (filter.isInstrumentedClass(ci) ? new IDIV(): super.idiv());
	  }

	  @Override
	  public ISHL ishl() {
	    return (ISHL) (filter.isInstrumentedClass(ci) ? new ISHL(): super.ishl());
	  }

	  @Override
	  public ISHR ishr() {
	    return (ISHR) (filter.isInstrumentedClass(ci) ? new ISHR(): super.ishr());
	  }

	  @Override
	  public IUSHR iushr() {
	    return (IUSHR) (filter.isInstrumentedClass(ci) ? new IUSHR(): super.iushr());
	  }

	  @Override
	  public IXOR ixor() {
	    return (IXOR) (filter.isInstrumentedClass(ci) ? new IXOR(): super.ixor());
	  }

	  @Override
	  public IOR ior() {
	    return (IOR) (filter.isInstrumentedClass(ci) ? new IOR(): super.ior());
	  }

	  @Override
	  public IREM irem() {
	    return (IREM) (filter.isInstrumentedClass(ci) ? new IREM(): super.irem());
	  }

	  @Override
	  public IF_ICMPEQ if_icmpeq(int targetPc) {
		    return (IF_ICMPEQ) (filter.isInstrumentedClass(ci) ? new IF_ICMPEQ(targetPc): super.if_icmpeq(targetPc));
	  }

	  @Override
	  public IF_ICMPNE if_icmpne(int targetPc) {
		    return (IF_ICMPNE) (filter.isInstrumentedClass(ci) ? new IF_ICMPNE(targetPc): super.if_icmpne(targetPc));
	  }


	  @Override
	  public FADD fadd() {
	    return (FADD) (filter.isInstrumentedClass(ci) ? new FADD(): super.fadd());
	  }

	  @Override
	  public FDIV fdiv() {
	    return (FDIV) (filter.isInstrumentedClass(ci) ? new FDIV(): super.fdiv());
	  }

	  @Override
	  public FMUL fmul() {
	    return (FMUL) (filter.isInstrumentedClass(ci) ? new FMUL(): super.fmul());
	  }

	  @Override
	  public FNEG fneg() {
	    return (FNEG) (filter.isInstrumentedClass(ci) ? new FNEG(): super.fneg());
	  }

	  @Override
	  public FREM frem() {
	    return (FREM) (filter.isInstrumentedClass(ci) ? new FREM(): super.frem());
	  }

	  @Override
	  public FSUB fsub() {
	    return (FSUB) (filter.isInstrumentedClass(ci) ? new FSUB(): super.fsub());
	  }

	  @Override
	  public FCMPG fcmpg() {
	    return (FCMPG) (filter.isInstrumentedClass(ci) ? new FCMPG(): super.fcmpg())
	    		;
	  }

	  @Override
	  public FCMPL fcmpl() {
		    return (FCMPL) (filter.isInstrumentedClass(ci) ? new FCMPL(): super.fcmpl());
		  }

	  @Override
	  public DADD dadd() {
		    return (DADD) (filter.isInstrumentedClass(ci) ? new DADD(): super.dadd());
		  }

	  @Override
	  public DCMPG dcmpg() {
		    return (DCMPG) (filter.isInstrumentedClass(ci) ? new DCMPG(): super.dcmpg());
		  }

	  @Override
	  public DCMPL dcmpl() {
		    return (DCMPL) (filter.isInstrumentedClass(ci) ? new DCMPL(): super.dcmpl());
		  }

	  @Override
	  public DDIV ddiv() {
		    return (DDIV) (filter.isInstrumentedClass(ci) ? new DDIV(): super.ddiv());
		  }

	  @Override
	  public DMUL dmul() {
		    return (DMUL) (filter.isInstrumentedClass(ci) ? new DMUL(): super.dmul());
		  }

	  @Override
	  public DNEG dneg() {
		    return (DNEG) (filter.isInstrumentedClass(ci) ? new DNEG(): super.dneg());
		  }

	  @Override
	  public DREM drem() {
		    return (DREM) (filter.isInstrumentedClass(ci) ? new DREM(): super.drem());
		  }

	  @Override
	  public DSUB dsub() {
		    return (DSUB) (filter.isInstrumentedClass(ci) ? new DSUB(): super.dsub());
		  }

	  @Override
	  public LADD ladd() {
		    return (LADD) (filter.isInstrumentedClass(ci) ? new LADD(): super.ladd());
		  }

	  @Override
	  public LAND land() {
		    return (LAND) (filter.isInstrumentedClass(ci) ? new LAND(): super.land());
		  }

	  @Override
	  public LCMP lcmp() {
		    return (LCMP) (filter.isInstrumentedClass(ci) ? new LCMP(): super.lcmp());
		  }

	  @Override
	  public LDIV ldiv() {
		    return (LDIV) (filter.isInstrumentedClass(ci) ? new LDIV(): super.ldiv());
		  }

	  @Override
	  public LMUL lmul() {
		    return (LMUL) (filter.isInstrumentedClass(ci) ? new LMUL(): super.lmul());
		  }

	  @Override
	  public LNEG lneg() {
		    return (LNEG) (filter.isInstrumentedClass(ci) ? new LNEG(): super.lneg());
		  }

	  @Override
	  public LOR lor() {
		  return (LOR) (filter.isInstrumentedClass(ci) ? new LOR(): super.lor());
		  }

	  @Override
	  public LREM lrem() {
		  return (LREM) (filter.isInstrumentedClass(ci) ? new LREM(): super.lrem());
		  }

	  @Override
	  public LSHL lshl() {
		  return (LSHL) (filter.isInstrumentedClass(ci) ? new LSHL(): super.lshl());
		  }

	  @Override
	  public LSHR lshr() {
		  return (LSHR) (filter.isInstrumentedClass(ci) ? new LSHR(): super.lshr());
		  }

	  @Override
	  public LSUB lsub() {
		  return (LSUB) (filter.isInstrumentedClass(ci) ? new LSUB(): super.lsub());
		  }

	  @Override
	  public LUSHR lushr() {
		  return (LUSHR) (filter.isInstrumentedClass(ci) ? new LUSHR(): super.lushr());
		  }

	  @Override
	  public LXOR lxor() {
		  return (LXOR) (filter.isInstrumentedClass(ci) ? new LXOR(): super.lxor());
		  }

	  @Override
	  public I2D i2d() {
		  return (I2D) (filter.isInstrumentedClass(ci) ? new I2D(): super.i2d());
		  }

	  @Override
	  public D2I d2i() {
		  return (D2I) (filter.isInstrumentedClass(ci) ? new D2I(): super.d2i());
		  }

	  @Override
	  public D2L d2l() {
		  return (D2L) (filter.isInstrumentedClass(ci) ?  new D2L(): super.d2l());
		  }

	  @Override
	  public I2F i2f() {
		  return (I2F) (filter.isInstrumentedClass(ci) ?  new I2F(): super.i2f());
		  }

	  @Override
	  public L2D l2d() {
		  return (L2D) (filter.isInstrumentedClass(ci) ?  new L2D(): super.l2d());
		  }

	  @Override
	  public L2F l2f() {
		  return (L2F) (filter.isInstrumentedClass(ci) ?  new L2F(): super.l2f());
		  }

	  @Override
	  public F2L f2l() {
		  return (F2L) (filter.isInstrumentedClass(ci) ?  new F2L(): super.f2l());
		  }

	  @Override
	  public F2I f2i() {
		  return (F2I) (filter.isInstrumentedClass(ci) ?  new F2I(): super.f2i());
		  }

	  @Override
	  public LOOKUPSWITCH lookupswitch(int defaultTargetPc, int nEntries) {
		  return (LOOKUPSWITCH) (filter.isInstrumentedClass(ci) ?  new LOOKUPSWITCH(defaultTargetPc, nEntries): super.lookupswitch(defaultTargetPc, nEntries));
		  }

	  @Override
	  public TABLESWITCH tableswitch(int defaultTargetPc, int low, int high) {
		  return (TABLESWITCH) (filter.isInstrumentedClass(ci) ?  new TABLESWITCH(defaultTargetPc, low, high): super.tableswitch(defaultTargetPc, low, high));
		  }

	  @Override
	  public D2F d2f() {
		  return (D2F) (filter.isInstrumentedClass(ci) ?  new D2F(): super.d2f());
		  }

	  @Override
	  public F2D f2d() {
		  return (F2D) (filter.isInstrumentedClass(ci) ?  new F2D(): super.f2d());
		  }

	  @Override
	  public I2B i2b() {
		  return (I2B) (filter.isInstrumentedClass(ci) ?  new I2B(): super.i2b());
		  }

	  @Override
	  public gov.nasa.jpf.jvm.bytecode.I2C i2c() {
		  return (gov.nasa.jpf.jvm.bytecode.I2C) (filter.isInstrumentedClass(ci) ?  new I2C(): super.i2c());
		  }

	  @Override
	  public I2S i2s() {
		  return (I2S) (filter.isInstrumentedClass(ci) ?  new I2S(): super.i2s());
		  }

	  @Override
	  public I2L i2l() {
		  return (I2L) (filter.isInstrumentedClass(ci) ?  new I2L(): super.i2l());
		  }

	  @Override
	  public L2I l2i() {
		  return (L2I) (filter.isInstrumentedClass(ci) ?  new L2I(): super.l2i());
		  }

	  @Override
	  public GETFIELD getfield(String fieldName, String clsName, String fieldDescriptor){
		  return (GETFIELD) (filter.isInstrumentedClass(ci) ?  new GETFIELD(fieldName, clsName, fieldDescriptor): super.getfield(fieldName, clsName, fieldDescriptor));
		  }
	  @Override
	  public GETSTATIC getstatic(String fieldName, String clsName, String fieldDescriptor){
		  return (GETSTATIC) (filter.isInstrumentedClass(ci) ?  new GETSTATIC(fieldName, clsName, fieldDescriptor): super.getstatic(fieldName, clsName, fieldDescriptor));
		  }

		//TODO: to review
        //From Fujitsu:

	  @Override
	  public NEW new_(String clsName) {
		  return (NEW) (filter.isInstrumentedClass(ci) ?  new NEW(clsName): super.new_(clsName));
		  }
	  @Override
	  public IFNONNULL ifnonnull(int targetPc) {
		  return (IFNONNULL) (filter.isInstrumentedClass(ci) ?  new IFNONNULL(targetPc): super.ifnonnull(targetPc));
		  }
	  @Override
	  public IFNULL ifnull(int targetPc) {
		  return (IFNULL) (filter.isInstrumentedClass(ci) ?  new IFNULL(targetPc): super.ifnull(targetPc));
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
