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

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.DynamicArea;
import gov.nasa.jpf.jvm.ElementInfo;
import gov.nasa.jpf.jvm.KernelState;
import gov.nasa.jpf.jvm.SystemState;
import gov.nasa.jpf.jvm.ThreadInfo;
import gov.nasa.jpf.jvm.bytecode.Instruction;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceClass;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceElem;
import gov.nasa.jpf.symbc.uberlazy.EquivalenceObjects;
import gov.nasa.jpf.symbc.uberlazy.PartitionChoiceGenerator;
import gov.nasa.jpf.symbc.uberlazy.UberLazyHelper;

public class IF_ACMPEQ extends gov.nasa.jpf.jvm.bytecode.IF_ACMPEQ {
	
	private boolean partition = false;
	private ChoiceGenerator<?> prevPartitionCG;
	private EquivalenceObjects equivObjs;
	private HashMap<Integer, ArrayList<EquivalenceElem>> partitionMethods;
	
	@Override
	public Instruction execute (SystemState ss, KernelState ks, ThreadInfo ti) {
		//System.out.println("coming to the IF_ACMPEQ bytecode in UberLazy");
		//int v1 = ti.peek();
		//int v2 = ti.peek(1);
		//System.out.println("v1 is " + v1);
		//System.out.println("v2 is " + v2);
		if(!ti.isFirstStepInsn()) {
			prevPartitionCG = UberLazyHelper.
							getPrevPartitionChoiceGenerator(ss.getChoiceGenerator());
			prevPartitionCG = (PartitionChoiceGenerator) prevPartitionCG;
			Object attr1 = ti.getOperandAttr();
			Object attr2 = ti.getOperandAttr(1);
			
		 	if(attr1 != null && attr2 != null) {
			
				equivObjs = UberLazyHelper.getEquivalenceObjects(prevPartitionCG);			
				EquivalenceClass eqClass1 = equivObjs.getEquivClass(attr1.toString());
				EquivalenceClass eqClass2 = equivObjs.getEquivClass(attr2.toString());
				// this where the partitioning logic occurs
				Object attr = ti.getTopFrame().getOperandAttr();
				if(attr != null) {
				//	System.out.println(attr.toString());
				}
				//System.exit(1);
				partitionMethods = new HashMap<Integer, ArrayList<EquivalenceElem>>(2);
				partitionMethods.put(0, new ArrayList<EquivalenceElem>());
				partitionMethods.put(1, new ArrayList<EquivalenceElem>());
				
				partitionElements(eqClass1, eqClass2);
				//partitionElements(eqClass2, v1);
				//System.out.println(partitionMethods.toString());
			}
		}
		return super.execute(ss, ks, ti);
	}
	
	private void partitionElements(EquivalenceClass eqClass1, EquivalenceClass eqClass2) {
		ArrayList<EquivalenceElem> eqElems1 = eqClass1.getElementsInEquivClass();
		ArrayList<EquivalenceElem> eqElems2 = eqClass1.getElementsInEquivClass();
		ArrayList<EquivalenceElem> trueElems = new ArrayList<EquivalenceElem>();
		ArrayList<EquivalenceElem> falseElems = new ArrayList<EquivalenceElem>();
		
		for(int elemIndex = 0; elemIndex < eqElems1.size(); elemIndex++) {
			EquivalenceElem elem1 = eqElems1.get(elemIndex);
			for(int secElemIndex = 0; secElemIndex < eqElems2.size(); secElemIndex++) {
				EquivalenceElem elem2 = eqElems2.get(secElemIndex);
			if(elem1.getAliasIdentifier().equals(elem2.getAliasIdentifier()) &&
					elem1.getTypeOfElement().equals(elem2.getTypeOfElement())) {
				//System.out.println("found 1");
				partition = true;
				trueElems.add(elem1);
				} else {
				falseElems.add(elem1);
				}
			}
		}
		
		partitionMethods.get(0).addAll(falseElems);
		partitionMethods.get(1).addAll(trueElems);
	}
}