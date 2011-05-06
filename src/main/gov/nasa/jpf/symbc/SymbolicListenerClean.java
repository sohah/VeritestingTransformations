
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

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.JVM;
import gov.nasa.jpf.jvm.MethodInfo;
import gov.nasa.jpf.jvm.StackFrame;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.bytecode.INVOKESTATIC;
import gov.nasa.jpf.symbc.concolic.PCAnalyzer;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicConstraintsGeneral;
import gov.nasa.jpf.util.Pair;


import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.StringTokenizer;
import java.util.Vector;



public class SymbolicListenerClean extends PropertyListenerAdapter implements PublisherExtension {

	/* Locals to preserve the value that was held by JPF prior to changing it
	 * in order to turn off state matching during symbolic execution
	 */
	private boolean retainVal = false;
	private boolean forcedVal = false;

	private Map<String,MethodSummary> allSummaries;
	private String currentMethodName = "";

	public SymbolicListenerClean(Config conf, JPF jpf) {
		jpf.addPublisherExtension(ConsolePublisher.class, this);
		allSummaries = new HashMap<String, MethodSummary>();
	}



	public void propertyViolated (Search search){


		JVM vm = search.getVM();

		SystemState ss = vm.getSystemState();
		ClassInfo ci = vm.getClassInfo();

			ChoiceGenerator <?>cg = vm.getChoiceGenerator();
			if (!(cg instanceof PCChoiceGenerator)){
				ChoiceGenerator <?> prev_cg = cg.getPreviousChoiceGenerator();
				while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
					prev_cg = prev_cg.getPreviousChoiceGenerator();
				}
				cg = prev_cg;
			}
			if ((cg instanceof PCChoiceGenerator) &&
				      ((PCChoiceGenerator) cg).getCurrentPC() != null){
				PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();
				String error = search.getLastError().getDetails();
				error = "\"" + error.substring(0,error.indexOf("\n")) + "...\"";

				if (SymbolicInstructionFactory.concolicMode) { //TODO: cleaner
					SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
					PCAnalyzer pa = new PCAnalyzer();
					pa.solve(pc,solver);
				}
				else
					pc.solve();
				Pair<String,String> pcPair = new Pair<String,String>(pc.stringPC(),error);//(pc.toString(),error);

				MethodSummary methodSummary = allSummaries.get(currentMethodName);
				methodSummary.addPathCondition(pcPair);
				allSummaries.put(currentMethodName,methodSummary);
				System.out.println("Property Violated: PC is "+pc.toString());
				System.out.println("Property Violated: result is  "+error);
				System.out.println("****************************");
			}
		//}
	}

	public void instructionExecuted(JVM vm) {

		if (!vm.getSystemState().isIgnored()) {
			Instruction insn = vm.getLastInstruction();
			SystemState ss = vm.getSystemState();
			ThreadInfo ti = vm.getLastThreadInfo();
			Config conf = vm.getConfig();

			if (insn instanceof InvokeInstruction) {
				InvokeInstruction md = (InvokeInstruction) insn;
				String methodName = md.getInvokedMethodName();
				int numberOfArgs = md.getArgumentValues(ti).length;
				MethodInfo mi = md.getInvokedMethod();
				ClassInfo ci = mi.getClassInfo();
				String className = ci.getName();

				if ((BytecodeUtils.isClassSymbolic(conf, className, mi, methodName))
						|| BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null)){

					retainVal = ss.getRetainAttributes();
					forcedVal = ss.isForced();
					//turn off state matching
					ss.setForced(true);
					//make sure it stays turned off when a new state is created
					ss.retainAttributes(true);


					MethodSummary methodSummary = new MethodSummary();
					String shortName = methodName;
					String longName = mi.getLongName();
					if (methodName.contains("("))
						shortName = methodName.substring(0,methodName.indexOf("("));
					methodSummary.setMethodName(shortName);
					Object [] args = md.getArgumentValues(ti);
					String argValues = "";
					for (int i=0; i<args.length; i++){
						argValues = argValues + args[i];
						if ((i+1) < args.length)
							argValues = argValues + ",";
					}
					methodSummary.setArgValues(argValues);
					String [] argTypeNames = md.getInvokedMethod(ti).getArgumentTypeNames();
					String argTypes = "";
					for (int j=0; j<argTypeNames.length; j++){
						argTypes = argTypes + argTypeNames[j];
						if ((j+1) < argTypeNames.length)
							argTypes = argTypes + ",";
					}
					methodSummary.setArgTypes(argTypes);


					//get the symbolic values (changed from constructing them here)
					StackFrame sf = ti.getTopFrame();
					String symValues = "";
					String symVarName = "";

					String[] names = mi.getLocalVariableNames();

					int sfIndex;


					if(names == null)
						throw new RuntimeException("ERROR: you need to turn debug option on");

					if (md instanceof INVOKESTATIC)
							sfIndex=0;
					else
						sfIndex=1; // do not consider implicit parameter "this"

					for(int i=0; i < numberOfArgs; i++){
						Expression expLocal = (Expression)sf.getLocalAttr(sfIndex);
						if (expLocal != null){ // symbolic
							symVarName = expLocal.toString();
							symValues = symValues + symVarName + ",";
						}
						else
							symVarName = names[sfIndex] + "_CONCRETE" + ",";

						    sfIndex++;
					}

					// get rid of last ","
					if (symValues.endsWith(",")) {
						symValues = symValues.substring(0,symValues.length()-1);
					}
					methodSummary.setSymValues(symValues);

					currentMethodName = longName;
					allSummaries.put(longName,methodSummary);
				}
			}else if (insn instanceof ReturnInstruction){
				MethodInfo mi = insn.getMethodInfo();
				ClassInfo ci = mi.getClassInfo();
				if (null != ci){
					String className = ci.getName();
					String methodName = mi.getName();
					String longName = mi.getLongName();
					int numberOfArgs = mi.getNumberOfArguments();

					if (((BytecodeUtils.isClassSymbolic(conf, className, mi, methodName))
							|| BytecodeUtils.isMethodSymbolic(conf, mi.getFullName(), numberOfArgs, null))){

						ss.retainAttributes(retainVal);
						ss.setForced(forcedVal);
						ChoiceGenerator <?>cg = vm.getChoiceGenerator();
						if (!(cg instanceof PCChoiceGenerator)){
							ChoiceGenerator <?> prev_cg = cg.getPreviousChoiceGenerator();
							while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
								prev_cg = prev_cg.getPreviousChoiceGenerator();
							}
							cg = prev_cg;
						}
						if ((cg instanceof PCChoiceGenerator) &&(
								(PCChoiceGenerator) cg).getCurrentPC() != null){
							PathCondition pc = ((PCChoiceGenerator) cg).getCurrentPC();

							if (SymbolicInstructionFactory.concolicMode) { //TODO: cleaner
								SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
								PCAnalyzer pa = new PCAnalyzer();
								pa.solve(pc,solver);
							}
							else
								pc.solve();

							String pcString = pc.stringPC();
							Pair<String,String> pcPair = null;

							String returnString = "";

							pcString = pc.toString();
							pcPair = new Pair<String,String>(pcString,returnString);
							MethodSummary methodSummary = allSummaries.get(longName);
							Vector<Pair> pcs = methodSummary.getPathConditions();
							if ((!pcs.contains(pcPair)) && (pcString.contains("SYM"))) {
								methodSummary.addPathCondition(pcPair);
							}
							allSummaries.put(longName,methodSummary);
							System.out.println("PC "+pc.toString());
							//System.out.println("Return is  "+returnString);
							System.out.println("****************************");
						}
					}
				}
			}
		}
	}

	  public void stateBacktracked(Search search) {

		  JVM vm = search.getVM();
		  Config conf = vm.getConfig();
		  Instruction insn = vm.getChoiceGenerator().getInsn();
		  SystemState ss = vm.getSystemState();
		  MethodInfo mi = insn.getMethodInfo();
		  String className = mi.getClassName();
		  String methodName = mi.getFullName();
		  //this method returns the number of slots for the arguments, including "this"
		  int numberOfArgs = mi.getNumberOfArguments();

		  if ((BytecodeUtils.isClassSymbolic(conf, className, mi, methodName))
					|| BytecodeUtils.isMethodSymbolic(conf, methodName, numberOfArgs, null)){
			//get the original values and save them for restoration after
			//we are done with symbolic execution
			retainVal = ss.getRetainAttributes();
			forcedVal = ss.isForced();
			//turn off state matching
			ss.setForced(true);
			//make sure it stays turned off when a new state is created
			ss.retainAttributes(true);
		  }
	  }

	  /*
	   *  todo: needs to be implemented if we are going to support heuristic search
	   */
	  public void stateRestored(Search search) {
		  System.err.println("Warning: State restored - heuristic search not supported");
	  }
	  /*
	   * Save the method summaries to a file for use by others
	   */
	  public void searchFinished(Search search) {
		  //writeTable();
//		  if (search.getConfig().getStringArray("symbolic.dp")[0].equalsIgnoreCase("compare")) {
//			  ProblemCompare.dump(search);
//		  }
	  }

	  /*
	   * The way this method works is specific to the format of the methodSummary
	   * data structure
	   */

	  //TODO:  needs to be changed not to use String representations
	  private void printMethodSummary(PrintWriter pw, MethodSummary methodSummary){


		  System.out.println("Symbolic values: " +methodSummary.getSymValues());
		  Vector<Pair> pathConditions = methodSummary.getPathConditions();
		  if (pathConditions.size() > 0){
			  Iterator it = pathConditions.iterator();
			  String allTestCases = "";
			  while(it.hasNext()){
				  String testCase = methodSummary.getMethodName() + "(";
				  Pair pcPair = (Pair)it.next();
				  String pc = (String)pcPair.a;
				  String errorMessage = (String)pcPair.b;
				  String symValues = methodSummary.getSymValues();
				  String argValues = methodSummary.getArgValues();
				  String argTypes = methodSummary.getArgTypes();

				  StringTokenizer st = new StringTokenizer(symValues, ",");
				  StringTokenizer st2 = new StringTokenizer(argValues, ",");
				  StringTokenizer st3 = new StringTokenizer(argTypes, ",");
				  while(st2.hasMoreTokens()){
					  String token = "";
					  String actualValue = st2.nextToken();
					  String actualType = st3.nextToken();
					  if (st.hasMoreTokens())
						  token = st.nextToken();
					  if (pc.contains(token)){
						  String temp = pc.substring(pc.indexOf(token));
						  String val = temp.substring(temp.indexOf("[")+1,temp.indexOf("]"));
						  if (actualType.equalsIgnoreCase("int") ||
								  actualType.equalsIgnoreCase("float") ||
								  actualType.equalsIgnoreCase("long") ||
								  actualType.equalsIgnoreCase("double"))
							  testCase = testCase + val + ",";
						  else{ //translate boolean values represented as ints
							  //to "true" or "false"
							  if (val.equalsIgnoreCase("0"))
								  testCase = testCase + "false" + ",";
							  else
								  testCase = testCase + "true" + ",";
						  }
					  }else{
						  //need to check if value is concrete
						  if (token.contains("CONCRETE"))
							  testCase = testCase + actualValue + ",";
						  else
							  testCase = testCase + "don't care,";
					  }
				  }
				  if (testCase.endsWith(","))
					  testCase = testCase.substring(0,testCase.length()-1);
				  testCase = testCase + ")";
				  //process global information and append it to the output

				  if (!errorMessage.equalsIgnoreCase(""))
					  testCase = testCase + "  --> " + errorMessage;
				  //do not add duplicate test case
				  if (!allTestCases.contains(testCase))
					  allTestCases = allTestCases + "\n" + testCase;
			  }
			  pw.println(allTestCases);
		  }else{
			  pw.println("No path conditions for " + methodSummary.getMethodName() +
					  "(" + methodSummary.getArgValues() + ")");
		  }
	  }


	  private void printMethodSummaryHTML(PrintWriter pw, MethodSummary methodSummary){
		  pw.println("<h1>Test Cases Generated by Symbolic JavaPath Finder for " +
				  methodSummary.getMethodName() + " (Path Coverage) </h1>");

		  Vector<Pair> pathConditions = methodSummary.getPathConditions();
		  if (pathConditions.size() > 0){
			  Iterator it = pathConditions.iterator();
			  String allTestCases = "";
			  String symValues = methodSummary.getSymValues();
			  StringTokenizer st = new StringTokenizer(symValues, ",");
			  while(st.hasMoreTokens())
				  allTestCases = allTestCases + "<td>" + st.nextToken() + "</td>";
			  allTestCases = "<tr>" + allTestCases + "</tr>\n";
			  while(it.hasNext()){
				  String testCase = "<tr>";
				  Pair pcPair = (Pair)it.next();
				  String pc = (String)pcPair.a;
				  String errorMessage = (String)pcPair.b;
				  //String symValues = methodSummary.getSymValues();
				  String argValues = methodSummary.getArgValues();
				  String argTypes = methodSummary.getArgTypes();
				  //StringTokenizer
				  st = new StringTokenizer(symValues, ",");
				  StringTokenizer st2 = new StringTokenizer(argValues, ",");
				  StringTokenizer st3 = new StringTokenizer(argTypes, ",");
				  while(st2.hasMoreTokens()){
					  String token = "";
					  String actualValue = st2.nextToken();
					  String actualType = st3.nextToken();
					  if (st.hasMoreTokens())
						  token = st.nextToken();
					  if (pc.contains(token)){
						  String temp = pc.substring(pc.indexOf(token));
						  String val = temp.substring(temp.indexOf("[")+1,temp.indexOf("]"));
						  if (actualType.equalsIgnoreCase("int") ||
								  actualType.equalsIgnoreCase("float") ||
								  actualType.equalsIgnoreCase("long") ||
								  actualType.equalsIgnoreCase("double"))
							  testCase = testCase + "<td>" + val + "</td>";
						  else{ //translate boolean values represented as ints
							  //to "true" or "false"
							  if (val.equalsIgnoreCase("0"))
								  testCase = testCase + "<td>false</td>";
							  else
								  testCase = testCase + "<td>true</td>";
						  }
					  }else{
						  //need to check if value is concrete
						  if (token.contains("CONCRETE"))
							  testCase = testCase + "<td>" + actualValue + "</td>";
						  else
							  testCase = testCase + "<td>don't care</td>";
					  }
				  }

				 //testCase = testCase + "</tr>";
				  //process global information and append it to the output


				  if (!errorMessage.equalsIgnoreCase(""))
					  testCase = testCase + "<td>" + errorMessage + "</td>";
				  //do not add duplicate test case
				  if (!allTestCases.contains(testCase))
					  allTestCases = allTestCases + testCase + "</tr>\n";
			  }
			  pw.println("<table border=1>");
			  pw.print(allTestCases);
			  pw.println("</table>");
		  }else{
			  pw.println("No path conditions for " + methodSummary.getMethodName() +
					  "(" + methodSummary.getArgValues() + ")");
		  }

	  }



      //	-------- the publisher interface
	  public void publishFinished (Publisher publisher) {
		String[] dp = SymbolicInstructionFactory.dp;
		if (dp[0].equalsIgnoreCase("no_solver") || dp[0].equalsIgnoreCase("cvc3bitvec"))
				return;

	    PrintWriter pw = publisher.getOut();

	    publisher.publishTopicStart("Method Summaries");
	    Iterator it = allSummaries.entrySet().iterator();
	    while (it.hasNext()){
	    	Map.Entry me = (Map.Entry)it.next();
	    	MethodSummary methodSummary = (MethodSummary)me.getValue();
	    	printMethodSummary(pw, methodSummary);
	    }

	    publisher.publishTopicStart("Method Summaries (HTML)");
	    it = allSummaries.entrySet().iterator();
	    while (it.hasNext()){
	    	Map.Entry me = (Map.Entry)it.next();
	    	MethodSummary methodSummary = (MethodSummary)me.getValue();
	    	printMethodSummaryHTML(pw, methodSummary);
	    }
	  }

	  protected class MethodSummary{
			private String methodName = "";
			private String argTypes = "";
			private String argValues = "";
			private String symValues = "";
			private Vector<Pair> pathConditions;

			public MethodSummary(){
			 	pathConditions = new Vector<Pair>();
			}

			public void setMethodName(String mName){
				this.methodName = mName;
			}

			public String getMethodName(){
				return this.methodName;
			}

			public void setArgTypes(String args){
				this.argTypes = args;
			}

			public String getArgTypes(){
				return this.argTypes;
			}

			public void setArgValues(String vals){
				this.argValues = vals;
			}

			public String getArgValues(){
				return this.argValues;
			}

			public void setSymValues(String sym){
				this.symValues = sym;
			}

			public String getSymValues(){
				return this.symValues;
			}

			public void addPathCondition(Pair pc){
				pathConditions.add(pc);
			}

			public Vector<Pair> getPathConditions(){
				return this.pathConditions;
			}

	  }
}

