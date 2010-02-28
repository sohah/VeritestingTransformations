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

import gov.nasa.jpf.JPFException;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.DynamicArea;
import gov.nasa.jpf.jvm.ElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.StackFrame;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceElem;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.PartitionChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;

public class GETFIELD extends gov.nasa.jpf.jvm.bytecode.GETFIELD {

  ChoiceGenerator<?> prevHeapCG;
  ArrayList<EquivalenceElem> aliasedElems;
  private boolean partition = false;
  
  @Override
  public Instruction execute (SystemState ss, KernelState ks, ThreadInfo ti) {

	  // if it is here then using the uberlazyInstructionfactory
	  // check whether the class hierarchies need to be constructed	  
	  if(TypeHierarchy.typeHierarchies == null) {
		  TypeHierarchy.buildTypeHierarchy(ti);
	  }

	  //original GETFIELD code from super
	  int objRef = ti.peek(); // don't pop yet, we might re-execute
	  lastThis = objRef;
	  if (objRef == -1) {
		  return ti.createAndThrowException("java.lang.NullPointerException",
				  "referencing field '" + fname + "' on null object");
	  }
	  ElementInfo ei = DynamicArea.getHeap().get(objRef);
	  FieldInfo fi = getFieldInfo();
	  if (fi == null) {
		  return ti.createAndThrowException("java.lang.NoSuchFieldError",
				  "referencing field '" + fname + "' in " + ei);
	  }
	  // check if this breaks the current transition
	  if (isNewPorFieldBoundary(ti, fi, objRef)) {
		  if (createAndSetFieldCG(ss, ei, ti)) {
			  return this;
		  }
	  }
	  //end GETFIELD code from super

	  Object attr = ei.getFieldAttr(fi);
	  // check if the field is of ref type & it is symbolic (i.e. it has an attribute)
	  // if it is we need to do lazy initialization

	//  if (!(fi.isReference() && attr != null)) {
	//	  return super.execute(ss,ks,ti);
	//  }
	  
	  if (!fi.isReference()) {
		  return super.execute(ss,ks,ti);
	  }
	  //this is where the uberlazy initialization begins.
	  int currentChoice;
	  ChoiceGenerator<?> thisHeapCG;

	  
	 
	  
	  if (!ti.isFirstStepInsn()) {
		  prevHeapCG = UberLazyHelper.getPrevPartitionChoiceGenerator
			(ss.getChoiceGenerator()); 

		  if(attr != null) {
			  partition = true;
				  aliasedElems = UberLazyHelper.getAllAliasedObjects
			  						(prevHeapCG, fi.getTypeClassInfo().getName());
			  thisHeapCG = new PartitionChoiceGenerator(2); // +null,new
			 
		  } else {
			  thisHeapCG = new PartitionChoiceGenerator(1); // no real choice
		  }
		 
		  ss.setNextChoiceGenerator(thisHeapCG);
		  return this;
	  } 

	  thisHeapCG = ss.getChoiceGenerator();
	  assert (thisHeapCG instanceof PartitionChoiceGenerator) :
		  "expected PartitionChoiceGenerator, got: " + thisHeapCG;
	  currentChoice = ((PartitionChoiceGenerator) thisHeapCG).getNextChoice();


	  PathCondition pcHeap = null; //this pc contains only the constraints on the heap
	  SymbolicInputHeap symInputHeap = null;
	  EquivalenceObjects equivObjs = null;

	  // pcHeap is updated with the pcHeap stored in the choice generator above
	  // get the pcHeap from the previous choice generator of the same type
	  if (prevHeapCG == null){
		  pcHeap = new PathCondition();
		  symInputHeap = new SymbolicInputHeap();
		  equivObjs = new EquivalenceObjects();	 
	  }
	  else {
		  pcHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentPCheap();
		  symInputHeap = ((HeapChoiceGenerator)prevHeapCG).getCurrentSymInputHeap();
		  equivObjs = ((PartitionChoiceGenerator) prevHeapCG).getCurrentEquivalenceObject();

	  }

	  assert pcHeap != null;
	  assert symInputHeap != null;
	  assert equivObjs != null;

	  // get the type of the field
	  ClassInfo typeClassInfo = fi.getTypeClassInfo(); 
	  //from original GETFIELD bytecode
	  ti.pop(); // Ok, now we can remove the object ref from the stack
	  int daIndex = 0; //index into JPF's dynamic area

	 if(partition) {
	  if (currentChoice == 0){ //null object
		  pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
		  daIndex = -1;
	  } 
	  else if (currentChoice == 1) { 
		  daIndex = UberLazyHelper.addNewHeapNode(typeClassInfo, ti, daIndex, attr, ks, pcHeap,
				  symInputHeap); // the last two args represent that the heap
		  								  // constraint does not need to be updated for
		  								  // any of the aliased objects
		  equivObjs.addClass(typeClassInfo.getName(), daIndex);	
		  equivObjs.addFieldName(fi.getFullName(), daIndex);
		  equivObjs.addAliasedObjects(daIndex, aliasedElems);
	  } 

	  ei.setReferenceField(fi,daIndex );
	  ei.setFieldAttr(fi, null);
    } 
    
	  ti.push( ei.getIntField(fi), fi.isReference());
	  ti.setOperandAttrNoClone(new String(fi.getFullName()));
	
	  ((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
	  ((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
	  ((PartitionChoiceGenerator)thisHeapCG).setEquivalenceObj(equivObjs);
	  return getNext(ti);

  }


  
 
  
}
