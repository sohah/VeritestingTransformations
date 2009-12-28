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

// An equivalence class is created for each symbolic variable of 
// complex data structure. The class contains all the possible
// data structure choices arising from either a new instantiation
// along the class heirarchy to account for polymorphism or choices
// arising from aliasing objects. 

public class EquivalenceClass implements Cloneable{
	String uniqueIdentifier;
	ArrayList<EquivalenceElem> elements;
	
	
	public EquivalenceClass(String uniqueIdentifier) {
		this.uniqueIdentifier = uniqueIdentifier;
		this.elements = new ArrayList<EquivalenceElem>();
	}
	
	public EquivalenceClass(String uniqueIdentifier,
					ArrayList<EquivalenceElem> elements) {
		this.uniqueIdentifier = uniqueIdentifier;
		this.elements = new ArrayList<EquivalenceElem>();
		this.elements.addAll(elements);
	}
	
	

	public boolean addElementToClass(String typeOfClass, String aliasInfo) {
		EquivalenceElem e = new EquivalenceElem(typeOfClass, aliasInfo);
		return elements.add(e);
	}
	
	public boolean addElementToClass(EquivalenceElem e) {
		return elements.add(e);
	}
	
	public String getUniqueIdOfEquivClass() {
		return uniqueIdentifier;
	}
	
	public ArrayList<EquivalenceElem> getElementsInEquivClass() {
		return elements;
	}
	
	public String toString() {
		String outputString = "Unique Id: " + uniqueIdentifier;
		for(int elemIndex = 0; elemIndex < elements.size(); elemIndex++) {
			outputString = outputString.concat(elements.get(elemIndex).toString());
		}
		return outputString;
	}
	
	public EquivalenceClass make_copy()  {
		EquivalenceClass eqClass = new EquivalenceClass(this.uniqueIdentifier);
		
		for (int elemIndex = 0; elemIndex < this.elements.size(); 
								elemIndex++) {
			EquivalenceElem elem = this.elements.get(elemIndex);
			eqClass.elements.add(elem.make_copy());
		}
		return eqClass;
	}
	
}