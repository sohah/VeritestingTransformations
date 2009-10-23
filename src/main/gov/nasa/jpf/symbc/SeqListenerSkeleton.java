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

import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.jvm.*;


import java.util.Vector;

public class SeqListenerSkeleton extends PropertyListenerAdapter {
	
	public void instructionExecuted(JVM vm) {
		//...
		Instruction insn = vm.getLastInstruction();
		SystemState ss = vm.getSystemState();
		ThreadInfo ti = vm.getLastThreadInfo();
		if (insn instanceof InvokeInstruction) {
			ChoiceGenerator [] cgs = vm.getSystemState().getChoiceGenerators();
			// cgs [0 .. cgs.length] should be the key
		}
	}
	
	public void stateBacktracked(Search search) {
		System.out.println(" BACKTRACKING ... ");
		ChoiceGenerator [] cgs = search.getVM().getSystemState().getChoiceGenerators();
		System.out.println(" with path "+ convert(search.getVM().getPath(), cgs));
	}

	public Vector<String> convert(Path path_from_jpf, ChoiceGenerator [] cgs){
		Vector<String> path = new Vector<String>();
		int path_length = path_from_jpf.size();
		Transition t;
		Step s;
      
		assert(cgs.length == path_from_jpf.size()); 
		// cgs should be synchronized with path_from_jpf
	
		for (int i = 1; i < path_length; i++) {
			t = path_from_jpf.get(i); // should check if t is null?
			// cgs [0 .. i] should be the key 
			int transition_length = t.getStepCount();
			for (int j = 0; j < transition_length; j++) {
				s = t.getStep(j);
				Instruction instr = s.getInstruction();
				if (instr instanceof InvokeInstruction) {
					InvokeInstruction md = (InvokeInstruction) instr;
					String methodName = md.getInvokedMethodName();
					
					// ...
					path.add(methodName);
				}
		    }
		}
		return path;
	}
}
	
