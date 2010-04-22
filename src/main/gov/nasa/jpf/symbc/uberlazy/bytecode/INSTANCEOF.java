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
import java.util.HashMap;

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceClass;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceElem;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.PartitionChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;


public class INSTANCEOF extends gov.nasa.jpf.jvm.bytecode.INSTANCEOF {
	
	private ChoiceGenerator<?> prevPartitionCG;
	private HashMap<Integer, EquivalenceClass> partitionForTypes;
	private EquivalenceObjects equivObjs;
	private int numPartitions = 1;
	private Object attr; 
	
	 @Override
	 public Instruction execute (SystemState ss, KernelState ks, ThreadInfo th) {
		 //System.out.println("this is instanceof operation");
		 int currentChoice;
		 ChoiceGenerator<?> currPartitionCG;

		 if (!th.isFirstStepInsn()) {
			 int objref = th.peek();
			 attr = th.getTopFrame().getOperandAttr();
		
			 prevPartitionCG = UberLazyHelper.
			 				getPrevPartitionChoiceGenerator(ss.getChoiceGenerator());
			 equivObjs = UberLazyHelper.getEquivalenceObjects(prevPartitionCG);
			 if(equivObjs != null) {
				 numPartitions = getNumberOfParititions(objref, ks);
				 currPartitionCG = new PartitionChoiceGenerator(numPartitions);
				 ss.setNextChoiceGenerator(currPartitionCG);
			 }
			 return this;
		 } 

		 int objref = th.pop(); 

		 if(prevPartitionCG == null || numPartitions == 1) {
			 if (objref == -1) {
				 th.push(0, false);
			 } else if (ks.da.get(objref).instanceOf(super.getType())) {
				 th.push(1, false);
			 } else {
				 th.push(0, false);
			 }
			 return getNext(th);
		 }


		 currPartitionCG = ss.getChoiceGenerator();
		 assert (currPartitionCG instanceof PartitionChoiceGenerator) : 
			 "expected PartitionChoiceGenerator, got: " + currPartitionCG;
		 currentChoice = ((PartitionChoiceGenerator) currPartitionCG).getNextChoice();

		 EquivalenceObjects currEqObjs = ((PartitionChoiceGenerator) prevPartitionCG).
		 													getCurrentEquivalenceObject();
		 PathCondition pcHeap = ((HeapChoiceGenerator) prevPartitionCG).getCurrentPCheap();
		 SymbolicInputHeap symInputHeap = ((HeapChoiceGenerator) prevPartitionCG).
		 														getCurrentSymInputHeap();



		 EquivalenceClass currPart = partitionForTypes.get(currentChoice);
		 currEqObjs.replaceClass(attr.toString(),currPart);
		 // currEqObjs.printAllEquivClasses();
		 EquivalenceElem elem = UberLazyHelper.getSuperParentInClassHierarchy
		 										(currEqObjs.getEquivClass(attr.toString()));
		 UberLazyHelper.generatingNewConcretization(objref, elem, symInputHeap, ks, th);
		 th.push(currentChoice,false);

		 ((PartitionChoiceGenerator) currPartitionCG).setEquivalenceObj(currEqObjs);
		 ((HeapChoiceGenerator)currPartitionCG).setCurrentPCheap(pcHeap);
		 ((HeapChoiceGenerator)currPartitionCG).setCurrentSymInputHeap(symInputHeap);
		 return getNext(th); 
	 }



	 private int getNumberOfParititions(int objref, KernelState ks) {
		 // the 2 indicate that it can either be true or false
		 partitionForTypes = UberLazyHelper.
		 		initializePartitionDataStructs(objref,2);
		 
		 if(equivObjs.getEquivClass(attr.toString()) != null) {
			 EquivalenceClass ec = equivObjs.getEquivClass(attr.toString());
	
			 ArrayList<EquivalenceElem> equivElements = 
				 ec.getElementsInEquivClass();
			 for(int eqIndex = 0; eqIndex < equivElements.size(); eqIndex++) {
				 EquivalenceElem equivElem = equivElements.get(eqIndex);
				 String typeName = equivElem.getTypeOfElement();
				 ClassInfo ci = ClassInfo.getResolvedClassInfo(typeName);
				 if(ci.isInstanceOf(super.getType())) {
					 //System.out.println(typeName  + " : " + ci.getType());
					 partitionForTypes.get(1).addElementToClass(equivElem);
				 } else {
					 //System.out.println(typeName + " is not an instanceof " + ci.getType());
					 partitionForTypes.get(0).addElementToClass(equivElem);
				 }
			 }
		 }
		 int notMatch = partitionForTypes.get(1).getElementsInEquivClass().size();
		 int doesMatch = partitionForTypes.get(0).getElementsInEquivClass().size();
		 if(notMatch > 0 && doesMatch > 0) {
			 return 2; 
		 } else {
			 return 1;
		 }
	 }



}