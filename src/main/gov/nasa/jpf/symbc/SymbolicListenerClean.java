//
//Copyright (C) 2007 United States Government as represented by the
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
package gov.nasa.jpf.symbc;

// does not work well for static methods:summary not printed for errors
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.JVM;
import gov.nasa.jpf.jvm.MethodInfo;
import gov.nasa.jpf.jvm.StackFrame;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.Types;
import gov.nasa.jpf.jvm.bytecode.IRETURN;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.bytecode.INVOKESTATIC;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.util.Pair;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Vector;

public class SymbolicListenerClean extends PropertyListenerAdapter implements PublisherExtension {


	Set<String> test_sequences = new HashSet<String>();; // here we print the test sequences
	private Map<String,MethodSummaryClean> allSummaries = new HashMap<String,MethodSummaryClean>();

	public SymbolicListenerClean(Config conf, JPF jpf) {
		jpf.addPublisherExtension(ConsolePublisher.class, this);
	}

	public void propertyViolated (Search search){
		//System.out.println("--------->property violated");
		JVM vm = search.getVM();
		SystemState ss = vm.getSystemState();
		ChoiceGenerator cg = vm.getChoiceGenerator();
		if (!(cg instanceof PCChoiceGenerator)){
			ChoiceGenerator prev_cg = cg.getPreviousChoiceGenerator();
			while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
				prev_cg = prev_cg.getPreviousChoiceGenerator();
			}
			cg = prev_cg;
		}
		String error = search.getLastError().getDetails();
		error = "\"" + error.substring(0,error.indexOf("\n")) + "...\"";
		if ((cg instanceof PCChoiceGenerator) &&
				      ((PCChoiceGenerator) cg).getCurrentPC() != null){

			PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
			//solve the path condition, then print it
			pc.solve();

            String sequence = "";
            // here we should get from the path all the choices that tell you the methods on the current path
			// with their arguments and their attributes (i.e. symbolic values)
			// get the solutions from the symbolic arguments
			// from here build the sequence and store it somewhere to be printed in the end
            // you can get the solution of a symbolic object by invoking solution()
            //IntegerExpression e;
            //e.solution();
            test_sequences.add(sequence);
			System.out.println("PC "+pc.toString());
		}
	}

	public void instructionExecuted(JVM vm) {

			Instruction insn = vm.getLastInstruction();
			SystemState ss = vm.getSystemState();
			ThreadInfo ti = vm.getLastThreadInfo();
			Config conf = vm.getConfig();

			if (insn instanceof InvokeInstruction && insn.isCompleted(ti)) {
				InvokeInstruction md = (InvokeInstruction) insn;
				String methodName = md.getInvokedMethodName();
				Object [] args = md.getArgumentValues(ti);
				int numberOfArgs = args.length;
				MethodInfo mi = md.getInvokedMethod();
				//  neha: changed methodName to full name
				if ((BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null))){
					// here we should remember the method name and the arguments
					// make sure we align concrete and symbolic arguments
					if (mi.isMJI())
						throw new RuntimeException("## Error:  native symbolic method not handled here!!!");

					String shortName = methodName;
					String longName = mi.getLongName();
					if (methodName.contains("("))
						shortName = methodName.substring(0,methodName.indexOf("("));
					System.out.println("long name" + longName);
					System.out.println("short name" + shortName);


					// print concrete values
					System.out.println("method name" + methodName);
					for (int i = 0; i < numberOfArgs; i++)
						System.out.println("args["+i+"]="+args[i]);

					// print symbolic values

					// code that gets the arg attributes
					// getArgAttributes should be a method mi or md
					// concrete args have null attributes
					//@@@@@@@@@@
					byte[] at = mi.getArgumentTypes();
					Object[] attrs = new Object[numberOfArgs];
					StackFrame sf = ti.getTopFrame();
					int count = 1 ; // we do not care about this
					if (md instanceof INVOKESTATIC)
						count = 0;  //no "this" reference
					for (int i = 0; i < numberOfArgs; i++) {
						attrs[i] = sf.getLocalAttr(count);
						count++;
						if(at[i]== Types.T_LONG || at[i] == Types.T_DOUBLE)
							count++;
					}
					//@@@@@@@@@@

					// end code that gets the arg attributes

					//Object[] attrsPeter = md.getArgumentAttrs(ti);
					for (int k=0; k < numberOfArgs; k++)
						System.out.println("attrs["+k+"]="+attrs[k]+ " ");
					MethodSummaryClean methodSummary = new MethodSummaryClean();

					methodSummary.argValues = args;
					methodSummary.symValues = attrs;
					methodSummary.methodName = shortName;
					allSummaries.put(longName,methodSummary);
				}
			}
			//else if (insn instanceof ReturnInstruction){
			// I don't think we need to do anything  here for printing test sequences...
			// but I'll put code for printing method summaries as in the original SymbolicListener
			//}


	}



	  public void stateBacktracked(Search search) {
		 // here do something similar to what you do when propertyViolated
	  }

      //	-------- the publisher interface
	  public void publishFinished (Publisher publisher) {
	    PrintWriter pw = publisher.getOut();
        // here just print the method sequences
	    publisher.publishTopicStart("Method Sequences");
	    Iterator<String> it = test_sequences.iterator();
	    while (it.hasNext())
	    	pw.println(it.next());
	  }

	  protected class MethodSummaryClean{
			private String methodName;
			private Object [] argValues;
			private Object [] symValues;
	  }
}
