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
package gov.nasa.jpf.symbc.uberlazy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.DynamicElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.symbc.heap.HeapNode;
import gov.nasa.jpf.symbc.heap.SymbolicInputHeap;

public class UberLazyHelper {
	
	public static boolean symbolicVariableExists(ChoiceGenerator<?> cg, int objref) {
		EquivalenceObjects equivObjs = ((PartitionChoiceGenerator) cg).
														getCurrentEquivalenceObject();
		if(equivObjs != null && equivObjs.getEquivClass(objref) != null) {
			return true;
		}
		return false;
	}
	
	public static HashMap<String, Set<String>> checkTypesForPrimitiveFields
									(ChoiceGenerator<?> cg, int objref, FieldInfo fi) {	
		HashMap<String, Set<String>> newPartitions = 
										new HashMap<String, Set<String>>();
		EquivalenceObjects equivObjs = ((PartitionChoiceGenerator) cg).
														getCurrentEquivalenceObject();
		EquivalenceClass eqClass = equivObjs.getEquivClass(objref);
		ArrayList<EquivalenceElem> elements = eqClass.getElementsInEquivClass();
		for(int elemIndex = 0; elemIndex < elements.size(); elemIndex++) {
			EquivalenceElem elem = elements.get(elemIndex);
			ClassInfo orig = ClassInfo.getResolvedClassInfo(elem.getTypeOfElement());
			boolean found = findMatchingFields(orig, orig, fi,newPartitions);
			ClassInfo ci = orig;
			// go up the class hierarchy to find the field 
			// when it is not found in the current class in java
			// since one class can inherit from a single class this works
			while(!found) {
				found = findMatchingFields(ci, orig, fi, newPartitions);
				ci = ci.getSuperClass();
			}
			//System.out.println("=================================");
		}
		//System.out.println(newPartitions.toString());
		//System.exit(1);
		return newPartitions;
	}
	
	private static boolean findMatchingFields(ClassInfo ci, ClassInfo origCI, FieldInfo fi,
										HashMap<String, Set<String>> newPartitions) {
		boolean found = false;
		FieldInfo[] fields = ci.getDeclaredInstanceFields();
		for(int fieldIndex = 0; fieldIndex < fields.length; fieldIndex++) {
			//System.out.println(fields[fieldIndex].getName() + "--- fieldName");
			if(fields[fieldIndex].getName().equals(fi.getName())) {
				found = true;
				String typeKey = fields[fieldIndex].getType();
				Set<String> partition;
				if(newPartitions.containsKey(typeKey)) {
					 partition = newPartitions.get(typeKey);
				} else {
					 partition = new HashSet<String>();
				}
				partition.add(origCI.getName());
				newPartitions.put(typeKey, partition);
			}
		}
		return found;
	}
	
	 public static HashMap<Integer, EquivalenceClass> initializePartitionDataStructs
	 									(String objIdentifier, int numPartitions) {
		 HashMap<Integer, EquivalenceClass> partition = new 
		 							HashMap<Integer, EquivalenceClass>(numPartitions);
		 for(int index = 0; index < numPartitions; index++) {
			EquivalenceClass ec = new EquivalenceClass(objIdentifier);
			partition.put(index, ec);
		 }
		 return partition;
	 }
	 
	 public static HashMap<Integer, EquivalenceClass> initializePartitionDataStructs
	 												(int objIdentifier, int numPartitions) {
		return UberLazyHelper.initializePartitionDataStructs
										(Integer.toString(objIdentifier),numPartitions);
	 }
	 
	 public static HashMap<Integer, EquivalenceClass> initializePartitionsWithData(int objId,
			 							HashMap<String, Set<String>> partFunc) {
		 int numPartitions = partFunc.size();
		 return UberLazyHelper.initializePartitionDataStructs(objId, numPartitions);
	 }
	 
	 //TODO: need to test this method
	 public static EquivalenceElem getSuperParentInClassHierarchy(EquivalenceClass eqClass) {
		 ArrayList<EquivalenceElem> eqElems = eqClass.getElementsInEquivClass();
		 if(eqElems.size() <= 0) {
			 return null;
		 }
		 EquivalenceElem elem = eqElems.get(0);
		 ClassInfo parentClassInfo = ClassInfo.getResolvedClassInfo
		 													(elem.getTypeOfElement());
		 
		 for(int eqIndex = 0; eqIndex < eqElems.size(); eqIndex++) {
			 EquivalenceElem currElem = eqElems.get(eqIndex);
			 if(parentClassInfo.isInstanceOf(currElem.getTypeOfElement())) {
				 parentClassInfo = ClassInfo.getResolvedClassInfo
				 								(currElem.getTypeOfElement());
				 elem = eqElems.get(eqIndex);
			 }
		 }
		 return elem;
	 }
	 
	 //initializes a new concretization for object represented by EqivalenceElem -- "elem"
	 public static void generatingNewConcretization(int objref, EquivalenceElem elem,
			 SymbolicInputHeap symInputHeap, KernelState ks, ThreadInfo th) {
		 HeapNode n = symInputHeap.header();
		 while(null != n) {
			 if(objref == n.getIndex()) {
				 ClassInfo tClassInfo = ClassInfo.
				 					getResolvedClassInfo(elem.getTypeOfElement());
				 //replace in the symbolic world
				 n.replaceType(tClassInfo);
				 
				 //replace in the concrete world
				 DynamicElementInfo dei = ks.da.get(objref);
				 dei.restoreFields(tClassInfo.createInstanceFields());				 
				 return;
			 }
			 n = n.getNext();
		 }

 }
}