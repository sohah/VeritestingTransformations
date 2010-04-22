package gov.nasa.jpf.symbc.uberlazy;

import gov.nasa.jpf.jvm.MJIEnv;
import gov.nasa.jpf.jvm.ThreadInfo;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

public class EquivalenceObjects implements Cloneable{
	// the String denotes the unique identifier of a symbolic variable
	// that is a reference. the string is the full name of the field
	protected HashMap<String, EquivalenceClass> allEquivClasses;
	protected HeapShapeAnalysis shapeAnalyzer;
	
	public EquivalenceObjects () { 
		allEquivClasses = new HashMap<String, EquivalenceClass>();
		shapeAnalyzer = new HeapShapeAnalysis();
	}
	
	public void addClass(String className, String fieldIdentifier, int objRef) {
		// the objRef provides the unique index for recognizing a particular field
		EquivalenceClass equivClass = new EquivalenceClass(fieldIdentifier);
		ArrayList<String> subClassTypeNames = TypeHierarchy.
												getTypeElements(className);
		int subClassSize = subClassTypeNames.size();
		String objRefId = Integer.toString(objRef);
		equivClass.addElementToClass(className,objRefId);
		//System.out.println(className + " , "   + uniqueObjectId );
		for(int subIndex = 0; subIndex < subClassSize; subIndex++) {
			String subClassName = subClassTypeNames.get(subIndex);
			//System.out.println(subClassName + " , " + uniqueObjectId );
			EquivalenceElem equivElem = new EquivalenceElem(subClassName,objRefId);
			equivClass.addElementToClass(equivElem);
		}
		allEquivClasses.put(fieldIdentifier, equivClass);
	}
	

	
	public void addAliasedObjects(String fieldIdentifier, ArrayList<EquivalenceElem> aliasedElems) {
		if(allEquivClasses.containsKey(fieldIdentifier)) {
			EquivalenceClass eqClass = allEquivClasses.get(fieldIdentifier);
			eqClass.getElementsInEquivClass().addAll(aliasedElems);
		}
	}
	
	public void replaceClass(String fieldIdentifier, EquivalenceClass ec) {
		if(allEquivClasses.containsKey(fieldIdentifier)) {
			allEquivClasses.put(fieldIdentifier, ec);
		}
	}
	
	public EquivalenceClass getEquivClass(String fieldIdentifier) {
		if(allEquivClasses.containsKey(fieldIdentifier)) {
			return allEquivClasses.get(fieldIdentifier);
		}
		return null;
	}
	
	public boolean containsEquivClassForRef(String fieldIdentifier) {
		if(allEquivClasses.containsKey(fieldIdentifier)) {
			return true;
		}
		return false;
	}
	
	
	
	public ArrayList<String> checkDifferingShapes(Integer rootRef, String fieldName, ArrayList<String> aliases,
																						ThreadInfo ti) {
		HashMap<String, String> partition = new HashMap<String, String>();
		for(int aliasIndex = 0; aliasIndex < aliases.size(); aliasIndex++) {
			String aliasSucc  = aliases.get(aliasIndex);
			MJIEnv env = ti.getEnv();
			String uniqueStr = shapeAnalyzer.linearizeRootedHeap(env, rootRef, 
									Integer.valueOf(aliasSucc), fieldName);
			if(!partition.containsKey(uniqueStr)) {
				partition.put(uniqueStr, aliasSucc);
			}
		}
		ArrayList<String> vals = new ArrayList<String>();
		Iterator<String> strItr = partition.keySet().iterator();
		while(strItr.hasNext()) {
			String objRef = partition.get(strItr.next());
			vals.add(objRef);
		}
		return vals;
	}
	
	
	public void printAllEquivClasses(){
		Iterator<String> indxItr = allEquivClasses.keySet().iterator();
		while(indxItr.hasNext()) {
			EquivalenceClass ec = allEquivClasses.get(indxItr.next());
			System.out.println("Equivalence Classes \n" + ec.toString());
		}
		
	}
	
	 @SuppressWarnings("unchecked")
	public EquivalenceObjects make_copy() {
		EquivalenceObjects copy = new EquivalenceObjects();
		Iterator<String> itr = this.allEquivClasses.keySet().iterator();
		while(itr.hasNext()) {
			String key = itr.next();
			copy.allEquivClasses.put(key, this.allEquivClasses.get(key).
														make_copy());
		}
		copy.shapeAnalyzer = new HeapShapeAnalysis();
		copy.shapeAnalyzer.nameToIndex = (HashMap<String, Integer>) this.shapeAnalyzer.
												nameToIndex.clone();
		copy.shapeAnalyzer.linearizeShape = (HashMap<Integer, Integer>) this.shapeAnalyzer.
												linearizeShape.clone();
		copy.shapeAnalyzer.roots = (ArrayList<String>) this.shapeAnalyzer.roots.clone();
		copy.shapeAnalyzer.counter = this.shapeAnalyzer.counter;
		return copy;
		  
	}
}