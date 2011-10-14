/*
 * Copyright (C) 2006 United States Government as represented by the
 * Administrator of the National Aeronautics and Space Administration (NASA).
 * All Rights Reserved.
 * 
 * This software is distributed under the NASA Open Source Agreement (NOSA),
 * version 1.3. The NOSA has been approved by the Open Source Initiative. See
 * the file NOSA-1.3-JPF at the top of the distribution directory tree for the
 * complete NOSA document.
 * 
 * THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND,
 * EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY
 * WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY
 * IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR
 * FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE
 * ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO
 * THE SUBJECT SOFTWARE.
 */

package gov.nasa.jpf.symbc.probsym;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.ListenerAdapter;
import gov.nasa.jpf.search.*;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.JVM;
import gov.nasa.jpf.jvm.MJIEnv;
import gov.nasa.jpf.jvm.MethodInfo;
import gov.nasa.jpf.jvm.StackFrame;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.VMState;
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.LocalVariableInstruction;
import gov.nasa.jpf.jvm.bytecode.StoreInstruction;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

public class ProbSymListener extends ListenerAdapter {
  
  /*
   * Class data
   */
  
  private PrintWriter    out;
  private DependencyCalc depCalc;
  private static final boolean DEBUG = true;
  
  private static int totalConsraints = 0;
  private static int totalMinConstraints = 0;
  
  /*
   * Constructor
   */
  
  public ProbSymListener (Config conf) {
    out = new PrintWriter(System.out, true);
    depCalc = new DependencyCalc();
  }
  
  /*
   * Listener methods
   */
  
      
  public void stateAdvanced(Search search) {
	  PathCondition pc = getPC(search.getVM());
	  if (pc == null)
		  return;
	  PathCondition  minPC = depCalc.calcMinPC(pc);
	  if (pc != null && minPC != null) {
		totalConsraints += pc.count();
		totalMinConstraints += minPC.count();
	    //System.out.println("Old PC = " + pc);
		System.out.println("Reduction = " + ((float)minPC.count())/((float)pc.count()) + " " + minPC.count() + " " + pc.count());
	  } 
  }
  
  public void searchFinished(Search s) {
	  System.out.println("Ratio = " + totalMinConstraints + " / " + totalConsraints + 
			             " = " + (100 - ((float)totalMinConstraints/(float)totalConsraints)*100) + "% reduction");
  }
  
  public static PathCondition getPC(JVM vm) {
		ChoiceGenerator<?> cg = vm.getChoiceGenerator();
		PathCondition pc = null;

		if (!(cg instanceof PCChoiceGenerator)) {
			ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGenerator();
			while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
				prev_cg = prev_cg.getPreviousChoiceGenerator();
			}
			cg = prev_cg;
		}

		if ((cg instanceof PCChoiceGenerator) && cg != null) {
			pc = ((PCChoiceGenerator) cg).getCurrentPC();
		}
		return pc;
	}

	public static void printPC(JVM jvm) {
		PathCondition pc = getPC(jvm);
		if (pc != null) {
			pc.solve();
			System.out.println(pc);
		}
		else
			System.out.println("PC is null");
	}
  
}