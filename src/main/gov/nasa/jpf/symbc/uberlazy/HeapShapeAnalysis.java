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

import gov.nasa.jpf.jvm.ClassInfo;
import gov.nasa.jpf.jvm.FieldInfo;
import gov.nasa.jpf.jvm.MJIEnv;
import gov.nasa.jpf.jvm.ReferenceFieldInfo;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class HeapShapeAnalysis {
	HashMap<String, Integer> nameToIndex;
	HashMap<Integer, Integer> linearizeShape;
	HashMap<Integer, Integer> discovered;
	String sequence;
	ArrayList<String> roots; 
	int counter = 0;
	int uniqueCount = 0;
	
	public HeapShapeAnalysis() {
		nameToIndex = new HashMap<String, Integer>();
		linearizeShape = new HashMap<Integer, Integer>();
		roots = new ArrayList<String>();
		sequence = new String();
		discovered = new HashMap<Integer, Integer>();
	}
	
	public boolean isNewElement(String fName) {
		if(!nameToIndex.containsKey(fName)) {
			return true;
		}
		return false;
	}
	
	public int addNewElement(String fName) {
		int val = counter;
		counter++;
		nameToIndex.put(fName, val);
		return val;
	}
	
	public int replaceElement(String fName, String fId) {
		int value = nameToIndex.get(fName);
		nameToIndex.remove(fName);
		nameToIndex.put(fId, value);
		return value;
	}
	
	public int getUniqueIndex(String fName) {
		if(nameToIndex.containsKey(fName)) {
			return nameToIndex.get(fName);
		}
		return -1;
	}
	
	public void addRelationalEdge(int i, int j) {
		linearizeShape.put(i, j);
	}
	
	public void addRelationalEdgeToNull(int i) {
		linearizeShape.put(i, -1);
	}
	
	private String traverseRootedHeapAndGetSequence(MJIEnv env, int n, String currName, String orgFieldName, 
																			int rootRef, int aliasRef){
		Integer newVal = new Integer(n);
		if (!discovered.containsKey(newVal)){ // vertex v just discovered
			// discovery time for v - so put v into the hashset and open paranthesis

			discovered.put(newVal, uniqueCount);
			sequence += "{";
			sequence += Integer.toString(uniqueCount) + ":" + currName;
			uniqueCount++;
			
			if(n == -99) { // the node represents a new node initialized
				//System.out.println("this is the -1 we put for the new node");
				sequence += "}";
				return sequence;
			}

			// Now start traversing all undiscovered successors of v
			ClassInfo ci = env.getClassInfo(n);
			//System.out.println("the classInfo ci :" + ci.getName());
			FieldInfo[] fields = ci.getDeclaredInstanceFields();
			for (int i = 0; i < fields.length; i++)
				if (fields[i] instanceof ReferenceFieldInfo) {
					String fname = fields[i].getName();
					//System.out.println("field name " + fname);
					int temp = env.getReferenceField(n, fname);	
					if(fname.equals(orgFieldName) && n == rootRef) {
						//System.out.println("this is what we are trying to initialize");
						traverseRootedHeapAndGetSequence(env, aliasRef, fname, orgFieldName, 
																			rootRef, aliasRef);
					} else {
						if(temp != -1) {
							traverseRootedHeapAndGetSequence(env, temp, fname, orgFieldName,
																			rootRef, aliasRef);
						}
					}
				}
			// All undiscovered successors of v are discovered. We are finished with v.
			// finish time for v - so, close parenthesis.
			sequence += "}";
		}

		return sequence;
	}
	
	// linearization of the heap
	public String linearizeRootedHeap(MJIEnv env, int rootRef, int aliasRef, String fieldName){
		// the data-structure that tracks the visited objects
		discovered.clear();
		// "empty" the sequence
		sequence="";
		uniqueCount = 0;
		// get the sequence for this rooted heap.
		sequence = traverseRootedHeapAndGetSequence(env, rootRef, fieldName, 
																	fieldName, rootRef, aliasRef);
		return sequence;
	}

}