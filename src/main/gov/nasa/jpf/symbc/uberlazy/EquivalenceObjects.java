package gov.nasa.jpf.symbc.uberlazy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

public class EquivalenceObjects implements Cloneable{
	// the integer denotes the unique index of a symbolic variable
	// that is a reference. the integer is the index of the reference
	// in the dynamic area of the system state. 
	protected HashMap<Integer, EquivalenceClass> allEquivClasses;
	
	public EquivalenceObjects () { 
		allEquivClasses = new HashMap<Integer, EquivalenceClass>();
	}
	
	public void addClass(String className, int objRef) {
		// the objRef provides the unique index for recognizing a particular field
		String uniqueObjectId = Integer.toString(objRef);
		EquivalenceClass equivClass = new EquivalenceClass(uniqueObjectId);
		ArrayList<String> subClassTypeNames = TypeHierarchy.
												getTypeElements(className);
		int subClassSize = subClassTypeNames.size();
		equivClass.addElementToClass(className,uniqueObjectId);
		//System.out.println(className + " , "   + uniqueObjectId );
		for(int subIndex = 0; subIndex < subClassSize; subIndex++) {
			String subClassName = subClassTypeNames.get(subIndex);
			//System.out.println(subClassName + " , " + uniqueObjectId );
			EquivalenceElem equivElem = new EquivalenceElem(subClassName,uniqueObjectId);
			equivClass.addElementToClass(equivElem);
		}
		allEquivClasses.put(objRef, equivClass);
	}
	
	public void addAliasedObjects(int objref, ArrayList<EquivalenceElem> aliasedElems) {
		if(allEquivClasses.containsKey(objref)) {
			EquivalenceClass eqClass = allEquivClasses.get(objref);
			eqClass.getElementsInEquivClass().addAll(aliasedElems);
		}
	}
	
	public void replaceClass(int objref, EquivalenceClass ec) {
		if(allEquivClasses.containsKey(objref)) {
			allEquivClasses.put(objref, ec);
		}
	}
	
	public EquivalenceClass getEquivClass(int objRef) {
		if(allEquivClasses.containsKey(objRef)) {
			return allEquivClasses.get(objRef);
		}
		return null;
	}
	
	public boolean containsEquivClassForRef(int objRef) {
		if(allEquivClasses.containsKey(objRef)) {
			return true;
		}
		return false;
	}
	
	public void printAllEquivClasses(){
		Iterator<Integer> indxItr = allEquivClasses.keySet().iterator();
		while(indxItr.hasNext()) {
			EquivalenceClass ec = allEquivClasses.get(indxItr.next());
			System.out.println("Equivalence Classes \n" + ec.toString());
		}
		
	}
	
	 public EquivalenceObjects make_copy() {
		EquivalenceObjects copy = new EquivalenceObjects();
		Iterator<Integer> itr = this.allEquivClasses.keySet().iterator();
		while(itr.hasNext()) {
			Integer key = itr.next();
			copy.allEquivClasses.put(key, this.allEquivClasses.get(key).
														make_copy());
		}
		return copy;
		  
	}
}