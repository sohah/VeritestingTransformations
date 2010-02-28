//
// Copyright (C) 2006 United States Government as represented by the
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
package gov.nasa.jpf.symbc.uberlazy.bytecode;

// need to fix names

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.MethodInfo;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceClass;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceElem;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.PartitionChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;

public class INVOKEVIRTUAL extends gov.nasa.jpf.jvm.bytecode.INVOKEVIRTUAL {
	
	private ChoiceGenerator<?> prevPartitionCG;
	private EquivalenceObjects equivObjs;
	private HashMap<String, ArrayList<EquivalenceElem>> partitionMethods;
	private boolean partition = false; 

	@Override
	public Instruction execute(SystemState ss, KernelState ks, ThreadInfo th) {
		
		int currentChoice;
		ChoiceGenerator<?> thisPartitionCG;
		if (!th.isFirstStepInsn()) {
			int objRef = th.getCalleeThis( getArgSize());
			prevPartitionCG = UberLazyHelper.
								getPrevPartitionChoiceGenerator(ss.getChoiceGenerator());
			equivObjs = UberLazyHelper.getEquivalenceObjects(prevPartitionCG, objRef);

			if(equivObjs != null && equivObjs.containsEquivClassForRef(objRef)) {
				EquivalenceClass eqClass = equivObjs.getEquivClass(objRef);
				// this where the partitioning logic occurs
				ArrayList<EquivalenceElem> elems = eqClass.getElementsInEquivClass();
				partitionMethods = new HashMap<String, ArrayList<EquivalenceElem>>();
				for (int eqIndex = 0; eqIndex < elems.size(); eqIndex++) {
					ClassInfo ci = ClassInfo.getResolvedClassInfo(elems.get(eqIndex).getTypeOfElement());
					MethodInfo invoked = ci.getMethod(mname, true);
					String uniqueId = invoked.getSignature().concat(invoked.getClassName());
					ArrayList<EquivalenceElem> lstOfClasses;
					if(partitionMethods.containsKey(uniqueId)) {
						lstOfClasses = partitionMethods.get(uniqueId);
					} else {
						lstOfClasses = new ArrayList<EquivalenceElem>();
					}
					lstOfClasses.add(elems.get(eqIndex));
					partitionMethods.put(uniqueId, lstOfClasses);
				}
				th.getTopFrame().setOperandAttr(null);

				int numPartitions = partitionMethods.size();
				thisPartitionCG = new PartitionChoiceGenerator(numPartitions);
				ss.setNextChoiceGenerator(thisPartitionCG);
				partition = true;
				return this;
			} 
		} 
		
			// when the instruction is actually executed
			//System.out.println("executing the instruction");
			if(partition) {
				thisPartitionCG = ss.getChoiceGenerator();
				assert (thisPartitionCG instanceof PartitionChoiceGenerator) :
					"expected PartitionChoiceGenerator, got: " + thisPartitionCG;
				currentChoice = ((PartitionChoiceGenerator) thisPartitionCG).getNextChoice();


				PathCondition pcHeap = null; //this pc contains only the constraints on the heap
				SymbolicInputHeap symInputHeap = null;
				EquivalenceObjects equivObjs = null;

				// pcHeap is updated with the pcHeap stored in the choice generator above
				// get the pcHeap from the previous choice generator of the same type
				if (prevPartitionCG == null){
					pcHeap = new PathCondition();
					symInputHeap = new SymbolicInputHeap();
					equivObjs = new EquivalenceObjects();	 
				}
				else {
					pcHeap = ((HeapChoiceGenerator)prevPartitionCG).getCurrentPCheap();
					symInputHeap = ((HeapChoiceGenerator)prevPartitionCG).getCurrentSymInputHeap();
					equivObjs = ((PartitionChoiceGenerator) prevPartitionCG).getCurrentEquivalenceObject();

				}

				assert pcHeap != null;
				assert symInputHeap != null;
				assert equivObjs != null; 
				Iterator<String> unqItr = partitionMethods.keySet().iterator();
				int counter = 0;
				String key = null;
				while (counter <= currentChoice) {
					key = unqItr.next();
					counter++;
				}
				ArrayList<EquivalenceElem> invokedci = partitionMethods.get(key);
				int objRef = th.getCalleeThis( getArgSize());

				EquivalenceElem sParent = UberLazyHelper.getSuperParentInClassHeirarchy(invokedci, objRef);
				UberLazyHelper.generatingNewConcretization(objRef, sParent, symInputHeap, ks, th);
				equivObjs = UberLazyHelper.generateNewEquivalenceClass(equivObjs, objRef, invokedci);
				 
				((HeapChoiceGenerator)thisPartitionCG).setCurrentPCheap(pcHeap);
				((HeapChoiceGenerator)thisPartitionCG).setCurrentSymInputHeap(symInputHeap);
				((PartitionChoiceGenerator)thisPartitionCG).setEquivalenceObj(equivObjs);
			}
			BytecodeUtils.InstructionOrSuper nextInstr = BytecodeUtils.execute(this, ss, ks, th, true);
			
			if (nextInstr.callSuper) {
			return super.execute(ss, ks, th);
		} else {
			return nextInstr.inst;
		}
	}
}
