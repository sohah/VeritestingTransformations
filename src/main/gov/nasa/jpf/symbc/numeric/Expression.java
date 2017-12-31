/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */


//Copyright (C) 2005 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.

//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.

//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.


package gov.nasa.jpf.symbc.numeric;


import java.util.Map;
import java.util.LinkedList;


public abstract class Expression implements Comparable<Expression> {

	public void setHoleVarName(String holeVarName) {
		this.holeVarName = holeVarName;
	}
	public String getHoleVarName() {
		return holeVarName;
	}
	String holeVarName = "";

	public enum HoleType {
		LOCAL_INPUT("local_input"),
		LOCAL_OUTPUT("local_output"),
		INTERMEDIATE("intermediate"),
		NONE ("none"),
		CONDITION("condition"),
		NEGCONDITION("negcondition"),
		FIELD_INPUT("field_input"),
		FIELD_OUTPUT("field_output");

		private final String string;

		HoleType(String string) {
			this.string = string;
		}
	}

	public static LinkedList<String> trackedSymVars = new LinkedList<String>();
    public abstract String stringPC();
    public abstract void getVarsVals(Map<String,Object> varsVals);
	public abstract void accept(ConstraintExpressionVisitor visitor);
	public String prefix_notation() {throw new RuntimeException("error printing");}

	public HoleType getHoleType() {
		return holeType;
	}

	HoleType holeType = HoleType.NONE;

	public boolean isHole() {
		return isHole;
	}

	public void setHole(boolean hole, HoleType h) {
		isHole = hole; holeType = h;
		assert((isHole && holeType == HoleType.LOCAL_INPUT) ||
				(isHole && holeType == HoleType.LOCAL_OUTPUT) ||
				(isHole && holeType == HoleType.INTERMEDIATE) ||
				(isHole && holeType == HoleType.CONDITION) ||
				(isHole && holeType == HoleType.NEGCONDITION) ||
				(isHole && holeType == HoleType.FIELD_INPUT) ||
				(isHole && holeType == HoleType.FIELD_OUTPUT) ||
				(!isHole && holeType == HoleType.NONE));
	}

	protected boolean isHole = false;

	public void setLocalStackSlot(int localStackSlot) {
		assert(holeType == HoleType.LOCAL_INPUT || holeType == HoleType.LOCAL_OUTPUT);
		this.localStackSlot = localStackSlot;
	}
	public int getLocalStackSlot() {
		assert(holeType == HoleType.LOCAL_INPUT || holeType == HoleType.LOCAL_OUTPUT);
		return localStackSlot;
	}
	protected int localStackSlot = -1;

	public void setFieldInfo(IntegerExpression use, String className, String fieldName) {
		assert(holeType == HoleType.FIELD_INPUT || holeType == HoleType.FIELD_OUTPUT);
		assert(use.getHoleType() == HoleType.LOCAL_INPUT);
		fieldInfo = new FieldInfo(use, className, fieldName);
	}

	public FieldInfo getFieldInfo() {
		return fieldInfo;
	}

	public class FieldInfo {
		public IntegerExpression use;
		public String className, fieldName;

		public FieldInfo(IntegerExpression use, String className, String fieldName) {
			this.use = use;
			this.className = className;
			this.fieldName = fieldName;
		}
	}

	FieldInfo fieldInfo = null;
	
}
