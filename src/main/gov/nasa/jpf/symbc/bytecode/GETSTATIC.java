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
package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.ElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;

import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.string.StringExpression;
import gov.nasa.jpf.symbc.string.SymbolicStringBuilder;
//import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;

public class GETSTATIC extends gov.nasa.jpf.jvm.bytecode.GETSTATIC {
	public GETSTATIC(String fieldName, String clsName, String fieldDescriptor){
	    super(fieldName, clsName, fieldDescriptor);
	  }


	private HeapNode[] prevSymRefs; // previously initialized objects of same type: candidates for lazy init
	private int numSymRefs = 0; // # of prev. initialized objects
	private int numNewRefs = 0; // # of new reference objects to account for polymorphism (neha)
	ChoiceGenerator<?> prevHeapCG;
	 boolean abstractClass = false;


	@Override
	public Instruction execute (SystemState ss, KernelState ks, ThreadInfo ti) {
		Config conf = ti.getVM().getConfig();
		String[] lazy = conf.getStringArray("symbolic.lazy");
		if (lazy == null || !lazy[0].equalsIgnoreCase("true"))
			return super.execute(ss,ks,ti);

		//neha: check whether the subtypes from polymorphism need to added
		// when instantiating "new" objects during lazy-initialization.
		// the configuration allows to consider all subtypes during the
		// instantiation. In aliasing all subtypes are considered by default.
//TODO: fix
//		String subtypes = conf.getString("symbolic.lazy.subtypes", "false");
//		if(!subtypes.equals("false") &&
//				TypeHierarchy.typeHierarchies == null) {
//			TypeHierarchy.buildTypeHierarchy(ti);
//		}

		FieldInfo fi = getFieldInfo();
		if (fi == null) {
			return ti.createAndThrowException("java.lang.NoSuchFieldException",
					(className + '.' + fname));
		}

		ClassInfo ci = fi.getClassInfo();
		// start: not sure if this code should stay here
		//	    if (!mi.isClinit(ci) && requiresClinitCalls(ti, ci))
		//			  return ti.getPC();
		// end: not sure if this code should stay here

		ElementInfo ei = ks.statics.get(ci.getName());

		//end GETSTATIC code from super


		if(ei==null)
			return super.execute(ss,ks,ti);
		Object attr = ei.getFieldAttr(fi);


		if (!(fi.isReference() && attr != null && attr != Helper.SymbolicNull))
			return super.execute(ss,ks,ti);

		//if(fi.getTypeClassInfo().getName().equals("java.lang.String"))
		if(attr instanceof StringExpression || attr instanceof SymbolicStringBuilder)
				return super.execute(ss,ks,ti); // Strings are handled specially

		// else: lazy initialization

		int currentChoice;
		ChoiceGenerator<?> heapCG;

		//String fullType = fi.getType(); //fully qualified type of this ref field
		ClassInfo typeClassInfo = fi.getTypeClassInfo(); // use this instead of fullType


		// first time around
		if (!ti.isFirstStepInsn()) {
			prevSymRefs = null;
			numSymRefs = 0;
			prevHeapCG = null;

			prevHeapCG = ss.getChoiceGenerator();
			while (!((prevHeapCG == null) || (prevHeapCG instanceof HeapChoiceGenerator))) {
				  prevHeapCG = prevHeapCG.getPreviousChoiceGenerator();
			}

			if (prevHeapCG != null) {
					// collect candidates for lazy initialization
					  SymbolicInputHeap symInputHeap =
						  ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();

					  prevSymRefs = new HeapNode[symInputHeap.count()]; // estimate of size; should be changed
					  HeapNode n = symInputHeap.header();
					  while (null != n){
						 // String t = (String)n.getType();
						  ClassInfo tClassInfo = n.getType();
						  //reference only objects of same type
						  // now we handle sub-classing
						  //if (fullType.equals(t)){
						  //if (typeClassInfo.isInstanceOf(tClassInfo)) {
						  if (tClassInfo.isInstanceOf(typeClassInfo)) {
							  prevSymRefs[numSymRefs] = n;
							  numSymRefs++;
						  }
						  n = n.getNext();
					  }
			}
			int increment = 2;
			if(typeClassInfo.isAbstract()) {
				abstractClass = true;
				increment = 1; // only null
			}
			// TODO: fix
//			if(!subtypes.equals("false")) {
//				// get the number of subtypes that exist, and add the number in
//				// the choice generator in addition to the ones that were there
//				numNewRefs = TypeHierarchy.getNumOfElements(typeClassInfo.getName());
//				heapCG = new HeapChoiceGenerator(numSymRefs+increment+numNewRefs); // +null,new
//			} else {
				heapCG = new HeapChoiceGenerator(numSymRefs+2);  //+null,new
			//}
			ss.setNextChoiceGenerator(heapCG);
			return this;
		} else {  // this is what really returns results
			heapCG = ss.getChoiceGenerator();
			assert (heapCG instanceof HeapChoiceGenerator) : "expected HeapChoiceGenerator, got: " + heapCG;
			currentChoice = ((HeapChoiceGenerator)heapCG).getNextChoice();
		}

		PathCondition pcHeap; //this pc contains only the constraints on the heap
		SymbolicInputHeap symInputHeap;

		// pcHeap is updated with the pcHeap stored in the choice generator above
		// get the pcHeap from the previous choice generator of the same type

		if (prevHeapCG == null){
			pcHeap = new PathCondition();
			symInputHeap = new SymbolicInputHeap();
		}
		else {
			pcHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentPCheap();
			symInputHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();
		}
		assert pcHeap != null;
		assert symInputHeap != null;



		int daIndex = 0; //index into JPF's dynamic area
		if (currentChoice < numSymRefs) { // lazy initialization
			  HeapNode candidateNode = prevSymRefs[currentChoice];
			  // here we should update pcHeap with the constraint attr == candidateNode.sym_v
			  pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, candidateNode.getSymbolic());
	          daIndex = candidateNode.getIndex();
		}
		else if (currentChoice == numSymRefs) { //existing (null)
			pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
			daIndex = -1;
		} else if (currentChoice == (numSymRefs + 1) && !abstractClass) {
			  // creates a new object with all fields symbolic and adds the object to SymbolicHeap
			  daIndex = Helper.addNewHeapNode(typeClassInfo, ti, daIndex, attr, ks, pcHeap,
					  		symInputHeap, numSymRefs, prevSymRefs);
		  } else {
			  //TODO: fix
			  System.err.println("subtyping not handled");
//			  int counter;
//			  if(abstractClass) {
//					counter = currentChoice - (numSymRefs+1) ; //index to the sub-class
//			  } else {
//					counter = currentChoice - (numSymRefs+1) - 1;
//			  }
//			  ClassInfo subClassInfo = TypeHierarchy.getClassInfo(typeClassInfo.getName(), counter);
//			  daIndex = Helper.addNewHeapNode(subClassInfo, ti, daIndex, attr, ks, pcHeap,
//					  		symInputHeap, numSymRefs, prevSymRefs);
		  }


		ei.setReferenceField(fi,daIndex );
		ei.setFieldAttr(fi, Helper.SymbolicNull); // was null
		ti.push( ei.getReferenceField(fi), fi.isReference());
		((HeapChoiceGenerator)heapCG).setCurrentPCheap(pcHeap);
		((HeapChoiceGenerator)heapCG).setCurrentSymInputHeap(symInputHeap);
		if (SymbolicInstructionFactory.debugMode)
			System.out.println("GETSTATIC pcHeap: " + pcHeap);
		return getNext(ti);
	}


}

