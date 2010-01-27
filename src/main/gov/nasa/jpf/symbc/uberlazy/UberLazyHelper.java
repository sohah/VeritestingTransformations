package gov.nasa.jpf.symbc.uberlazy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.DynamicElementInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.Fields;
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
				 //ks.da.replaceObject(tClassInfo, th, objref);
				 
				 //DynamicElementInfo dei = ks.da.get(objref);
				 //Fields f = dei.getFields();
				 tClassInfo.createInstanceFields();
			
				// tClassInfo.getinitializeInstanceData()
				 return;
			 }
			 n = n.getNext();
		 }

 }
}