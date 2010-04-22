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

import java.util.ArrayList;

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.uberlazy.EqualityOfClasses;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceElem;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.PartitionChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;

public class IF_ACMPNE extends gov.nasa.jpf.jvm.bytecode.IF_ACMPNE {
	private boolean partition = false;
	private ChoiceGenerator<?> prevPartitionCG;
	private ArrayList<EqualityOfClasses> partitionVals;

	@Override
	public Instruction execute (SystemState ss, KernelState ks, ThreadInfo ti) {
		
		int currentChoice;
		ChoiceGenerator<?> thisPartitionCG;
		if(!ti.isFirstStepInsn()) {
			prevPartitionCG = UberLazyHelper.
			getPrevPartitionChoiceGenerator(ss.getChoiceGenerator());
			prevPartitionCG = (PartitionChoiceGenerator) prevPartitionCG;
			Object attr1 = ti.getOperandAttr();
			Object attr2 = ti.getOperandAttr(1);

			if(attr1 != null && attr2 != null) {
				partitionVals = RefComparision.computePartitions
				(prevPartitionCG, attr1, attr2);
				int numPartitions = partitionVals.size();
				thisPartitionCG = new PartitionChoiceGenerator(numPartitions);
				ss.setNextChoiceGenerator(thisPartitionCG);
				partition = true;
				return this;

			}
		}

		if(!partition) {
			return super.execute(ss, ks, ti);
		} 

		ti.pop();
		ti.pop();

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

		EqualityOfClasses eqOfClasses = partitionVals.get(currentChoice);

		EquivalenceElem sParent1 = UberLazyHelper.getSuperParentInClassHeirarchy(eqOfClasses.getFirstClass().
				getElementsInEquivClass());
		EquivalenceElem sParent2 = UberLazyHelper.getSuperParentInClassHeirarchy(eqOfClasses.getSecondClass().
				getElementsInEquivClass());

		UberLazyHelper.generatingNewConcretization(Integer.valueOf(sParent1.getAliasIdentifier()), sParent1,
				symInputHeap, ks, ti);
		UberLazyHelper.generatingNewConcretization(Integer.valueOf(sParent2.getAliasIdentifier()), sParent2,
				symInputHeap, ks, ti);

		equivObjs.replaceClass(eqOfClasses.getFirstClass().getUniqueIdOfEquivClass(), eqOfClasses.getFirstClass());
		equivObjs.replaceClass(eqOfClasses.getSecondClass().getUniqueIdOfEquivClass(), eqOfClasses.getSecondClass());


		((HeapChoiceGenerator)thisPartitionCG).setCurrentPCheap(pcHeap);
		((HeapChoiceGenerator)thisPartitionCG).setCurrentSymInputHeap(symInputHeap);
		((PartitionChoiceGenerator)thisPartitionCG).setEquivalenceObj(equivObjs);

		if (eqOfClasses.bothAreEqual()) {
			return getTarget();
		} else {
			return getNext(ti);
		}
	}
}