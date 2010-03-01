package gov.nasa.jpf.symbc.uberlazy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

public class EquivalenceObjects implements Cloneable{
	// the String denotes the unique identifier of a symbolic variable
	// that is a reference. the string is the full name of the field
	protected HashMap<String, EquivalenceClass> allEquivClasses;
	//
	
	public EquivalenceObjects () { 
		allEquivClasses = new HashMap<String, EquivalenceClass>();
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
	
	public void printAllEquivClasses(){
		Iterator<String> indxItr = allEquivClasses.keySet().iterator();
		while(indxItr.hasNext()) {
			EquivalenceClass ec = allEquivClasses.get(indxItr.next());
			System.out.println("Equivalence Classes \n" + ec.toString());
		}
		
	}
	
	 public EquivalenceObjects make_copy() {
		EquivalenceObjects copy = new EquivalenceObjects();
		Iterator<String> itr = this.allEquivClasses.keySet().iterator();
		while(itr.hasNext()) {
			String key = itr.next();
			copy.allEquivClasses.put(key, this.allEquivClasses.get(key).
														make_copy());
		}
		return copy;
		  
	}
}