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

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.EqualityOfClasses;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceClass;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceElem;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;

import java.util.ArrayList;

public class RefComparision {
	
	public static ArrayList<EqualityOfClasses> computePartitions (ChoiceGenerator<?> prevPartitionCG,
																			Object attr1, Object attr2) {
		ArrayList<EqualityOfClasses> partitionVals = new ArrayList<EqualityOfClasses>();
		EquivalenceObjects equivObjs = UberLazyHelper.getEquivalenceObjects(prevPartitionCG);			
		EquivalenceClass eqClass1 = equivObjs.getEquivClass(attr1.toString());
		EquivalenceClass eqClass2 = equivObjs.getEquivClass(attr2.toString());
		// this where the partitioning logic occurs
		//System.out.println(attr1.toString() + " ----" + attr2.toString());
		ArrayList<String> uniqueRefs1 = UberLazyHelper.getUniqueObjReferences
		(eqClass1.getElementsInEquivClass());
		ArrayList<String> uniqueRefs2 = UberLazyHelper.getUniqueObjReferences
		(eqClass2.getElementsInEquivClass());

		for(int refId = 0; refId < uniqueRefs1.size(); refId++) {
			String firstElem = uniqueRefs1.get(refId);
			for(int otherId = 0; otherId < uniqueRefs2.size(); otherId++) {
				String secondElem = uniqueRefs2.get(otherId);
				EquivalenceClass newClass1 = new EquivalenceClass(eqClass1.getUniqueIdOfEquivClass());
				EquivalenceClass newClass2 = new EquivalenceClass(eqClass2.getUniqueIdOfEquivClass());
				ArrayList<EquivalenceElem> newElems1 = UberLazyHelper.getEquivalenceElemsGivenObjRef(firstElem,
						eqClass1.getElementsInEquivClass());
				ArrayList<EquivalenceElem> newElems2 = UberLazyHelper.getEquivalenceElemsGivenObjRef(secondElem,
						eqClass2.getElementsInEquivClass());
				newClass1.addElementsToClass(newElems1);
				newClass2.addElementsToClass(newElems2);

				EqualityOfClasses eqOfClasses;
				if(firstElem.equals(secondElem)) {
					//System.out.println("match :[" + firstElem + " , " + secondElem + "]" );
					eqOfClasses = new EqualityOfClasses(newClass1, newClass2, true);
				} else {
					//System.out.println("does not match :[" + firstElem + " , " + secondElem + "]");
					eqOfClasses = new EqualityOfClasses(newClass1, newClass2, false);
				}
				partitionVals.add(eqOfClasses);
			}
		}
		return partitionVals;
	}
	
}