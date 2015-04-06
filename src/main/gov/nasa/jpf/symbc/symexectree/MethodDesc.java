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

/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

import gov.nasa.jpf.vm.MethodInfo;


/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class MethodDesc {

	private final String methodName;
	private final int argsNum;
	
	public MethodDesc(String methodName, int argsNum) {
		this.methodName = methodName;
		this.argsNum = argsNum;
	}
	
	public MethodDesc(MethodInfo mi) {
		this.methodName = mi.getBaseName();
		this.argsNum = mi.getNumberOfArguments();
	}
	
	public String getMethodName() {
		return methodName;
	}
	
	//TODO: make a more appropriate short name used for the templates
	public String getShortMethodName() {
		String shortName = this.methodName.substring(this.methodName.lastIndexOf('.') + 1, this.methodName.length());
		return shortName + "_" + this.argsNum + "_";
	}

	public int getArgsNum() {
		return argsNum;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + argsNum;
		result = prime * result
				+ ((methodName == null) ? 0 : methodName.hashCode());
		return result;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		MethodDesc other = (MethodDesc) obj;
		if (argsNum != other.argsNum)
			return false;
		if (methodName == null) {
			if (other.methodName != null)
				return false;
		} else if (!methodName.equals(other.methodName))
			return false;
		return true;
	}
	
	@Override
	public String toString() {
		return methodName + "(" + this.argsNum + ")";
	}
}
