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
import java.util.Iterator;
import java.util.Set;

import gov.nasa.jpf.JPFException;
import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.DynamicArea;
import gov.nasa.jpf.jvm.ElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.heap.HeapChoiceGenerator;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.Helper;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;
import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceClass;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.PartitionChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.TypeHierarchy;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;

public class GETFIELD extends gov.nasa.jpf.jvm.bytecode.GETFIELD {

  ChoiceGenerator<?> prevHeapCG;
  private HashMap<String, Set<String>> primitivePartition;
  private HashMap<Integer, EquivalenceClass> partitionForTypes;
  private EquivalenceObjects equivObjs;
  private boolean isReference = false;

  
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
	  
	  //System.out.println("the position number is:" + this.position);

	  // the field is not symbolic return as is
	  if(attr == null) {
		  return super.execute(ss, ks, ti);
	  }
	  
	  if(fi.isReference()) {
		  //System.out.println("it is a reference");
		  isReference = true;
	  }
	
	  ChoiceGenerator<?> thisHeapCG;
		
	  if (!ti.isFirstStepInsn()) {
		 
		  if(isReference) {
			  thisHeapCG = new PartitionChoiceGenerator(2); // +null,new
			  ss.setNextChoiceGenerator(thisHeapCG);
		  } else {
			  prevHeapCG = ss.getChoiceGenerator();
			  while (!((prevHeapCG == null) || (prevHeapCG instanceof PartitionChoiceGenerator))) {
				  prevHeapCG = prevHeapCG.getPreviousChoiceGenerator();
			  }
			  if(prevHeapCG != null &&
					  UberLazyHelper.symbolicVariableExists(prevHeapCG, objRef)) {
				  equivObjs = ((PartitionChoiceGenerator) prevHeapCG).getCurrentEquivalenceObject(); 
				  primitivePartition = 
					  	UberLazyHelper.checkTypesForPrimitiveFields(prevHeapCG, objRef,fi);
				  thisHeapCG = new PartitionChoiceGenerator(primitivePartition.size());
				  partitionForTypes = UberLazyHelper.initializePartitionsWithData(objRef,
						  													primitivePartition);
				  ss.setNextChoiceGenerator(thisHeapCG);
			  } 
		  }
		  return this;
	  } 

	  int currentChoice;
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
	 
	  if(isReference) {
		  handleReference(ss, ks, ti, attr, ei, pcHeap,
				  symInputHeap, equivObjs, currentChoice);
	  } else {
		  handlePrimitive(ss, ks, ti, attr, ei, pcHeap,
				  symInputHeap, equivObjs, currentChoice, objRef);
	  }
	  
	  ((HeapChoiceGenerator)thisHeapCG).setCurrentPCheap(pcHeap);
	  ((HeapChoiceGenerator)thisHeapCG).setCurrentSymInputHeap(symInputHeap);
	  ((PartitionChoiceGenerator)thisHeapCG).setEquivalenceObj(equivObjs);
	  
	  if(isReference) {
		  return getNext(ti);
	  } else {
		  return super.execute(ss, ks, ti);
	  }
	 
  }
  
  private void handlePrimitive(SystemState ss, KernelState ks, ThreadInfo ti, Object attr, ElementInfo ei,
		  PathCondition pcHeap, SymbolicInputHeap symInputHeap, EquivalenceObjects equivObjs, int currentChoice,
		  																					int objref) {
	  int counter = 0;
	  Iterator<String> itr = primitivePartition.keySet().iterator();
	  while(counter < currentChoice) {
		  System.out.println("counter :" + counter);
		  itr.next();
		  counter++;
	  }
	  if(itr.hasNext()) {
		  Set<String> vals = primitivePartition.get(itr.next());
		  // case 1: if you are executing the concrete one
		  String typeClassInfo = ei.getClassInfo().getName();
		  System.out.println("The typeClassInfo is :" + typeClassInfo);
		  if(vals.contains(typeClassInfo) || vals.size() <= 0) {
			  System.out.println("found the type");
			  // do nothing 
			  return;
		  } else if(vals.size() == 1) { //case 2 only a single
			   EquivalenceObjects objs = new EquivalenceObjects();
			   
		  }
		  Iterator<String> strItr = vals.iterator();
		  while(strItr.hasNext()) {
			  System.out.println(strItr.next() );
		  }
		  System.out.println();
	  }
	  //TODO update the EquivalenceObject and change the object on the heap 
	  //look at the instanceof operator to check how the object can be updated
	  
	  
  }
  
  private void handleReference(SystemState ss, KernelState ks, ThreadInfo ti, Object attr, 
		  							ElementInfo ei, PathCondition pcHeap, SymbolicInputHeap symInputHeap,
		  							EquivalenceObjects equivObjs, int currentChoice) {
	
	  // get the type of the field
	  ClassInfo typeClassInfo = fi.getTypeClassInfo(); 
	  //from original GETFIELD bytecode
	  ti.pop(); // Ok, now we can remove the object ref from the stack
	  int daIndex = 0; //index into JPF's dynamic area
	 
	  if (currentChoice == 0){ //null object
		  pcHeap._addDet(Comparator.EQ, (SymbolicInteger) attr, new IntegerConstant(-1));
		  daIndex = -1;
	  } 
	  else if (currentChoice == 1) { 

		  daIndex = addNewHeapNode(typeClassInfo, ti, daIndex, attr, ks, pcHeap, symInputHeap);
		  equivObjs.addClass(typeClassInfo.getName(), daIndex);
		  
		  //System.out.println("the daIndex is :" + daIndex);
	  } 

	  ei.setReferenceField(fi,daIndex );
	  ei.setFieldAttr(fi, null);
	  ti.push( ei.getIntField(fi), fi.isReference());
	 
  }
  
  //TODO: Move this to a helper function where all sorts-of-lazy initialization
  // can access this method. 
  private int addNewHeapNode(ClassInfo typeClassInfo, ThreadInfo ti, int daIndex, Object attr,
		  KernelState ks, PathCondition pcHeap, SymbolicInputHeap symInputHeap) {
	  daIndex = ks.da.newObject(typeClassInfo, ti);
	  String refChain = ((SymbolicInteger) attr).getName() + "[" + daIndex + "]"; // do we really need to add daIndex here?
	  SymbolicInteger newSymRef = new SymbolicInteger( refChain);
	  ElementInfo eiRef = DynamicArea.getHeap().get(daIndex);
	  FieldInfo[] fields = typeClassInfo.getDeclaredInstanceFields();
	  Helper.initializeInstanceFields(fields, eiRef,refChain);
	  FieldInfo[] staticFields = typeClassInfo.getDeclaredStaticFields();
	  Helper.initializeStaticFields(staticFields, typeClassInfo, ti);
	  // create new HeapNode based on above info
	  // update associated symbolic input heap
	  HeapNode n= new HeapNode(daIndex,typeClassInfo,newSymRef);
	  symInputHeap._add(n);
	  pcHeap._addDet(Comparator.NE, newSymRef, new IntegerConstant(-1));
	  //pcHeap._addDet(Comparator.EQ, newSymRef, (SymbolicInteger) attr);
	  //TODO: for uberlazy we can't add the NE right here should be added later
	  // for (int i=0; i< numSymRefs; i++)
		//  pcHeap._addDet(Comparator.NE, n.getSymbolic(), prevSymRefs[i].getSymbolic());
	  return daIndex;
  }

  
}
