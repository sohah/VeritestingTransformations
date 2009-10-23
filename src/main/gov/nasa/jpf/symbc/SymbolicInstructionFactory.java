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
import gov.nasa.jpf.util.GenericInstructionFactory;

/*
 * Refactored version to use the GenericInstructionFactory
 */
public class SymbolicInstructionFactory extends GenericInstructionFactory {
	static public String[] dp;

	//bytecodes replaced by our symbolic implementation
	static final String[] BC_NAMES = {
		"IADD", "IAND", "IINC", "ISUB","IMUL","INEG",
		"IFLE","IFLT","IFGE","IFGT","IFEQ","IFNE",
		"INVOKESTATIC","INVOKEVIRTUAL",
		"IF_ICMPGE","IF_ICMPGT","IF_ICMPLE","IF_ICMPLT",
		"IDIV", "IXOR", "IOR", "IREM", "IF_ICMPEQ", "IF_ICMPNE","INVOKESPECIAL",
		"FADD", "FDIV", "FMUL", "FNEG","FREM", "FSUB", "FCMPG", "FCMPL",
        "DADD", "DCMPG", "DCMPL", "DDIV", "DMUL", "DNEG", "DREM", "DSUB",
        "LADD", "LAND", "LCMP", "LDIV", "LMUL", "LNEG", "LOR", "LREM",
        "LSHL", "LSHR", "LSUB", "LUSHR", "LXOR",
        "I2D" , "D2I" , "D2L", "I2F" , "L2D", "L2F" , "F2L" , "F2I",
        "LOOKUPSWITCH", "TABLESWITCH",
        "D2F", "F2D", "I2B", "I2C", "I2S", "I2L", "L2I"
        , "GETFIELD", "GETSTATIC"
        //TODO: to review
        //From Fujitsu:
        , "NEW", "IFNULL", "IFNONNULL"
	};

	//where the bytecodes reside
	protected static final String PKG_NAME = "gov.nasa.jpf.symbc.bytecode.";

	// what classes should use them
	protected static final String[] DEFAULT_EXCLUDES = { };

	public  SymbolicInstructionFactory (Config conf){
		super(conf, PKG_NAME, BC_NAMES, null, DEFAULT_EXCLUDES);

//		set the decision procedure to be used

		if (dp==null) {
			dp = conf.getStringArray("symbolic.dp");
			if (dp == null) {
				dp = new String[1];
				dp[0] = "choco";
			}
			System.out.println("symbolic.dp="+dp[0]);
		}


		System.out.println("Symbolic Execution Mode");
	}
}
