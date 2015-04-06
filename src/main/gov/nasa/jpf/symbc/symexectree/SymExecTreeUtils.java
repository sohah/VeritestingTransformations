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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SymExecTreeUtils {
	
	/*
	 * TODO: We should remove the use of the jpfConfig and replace it with a list of MethodDesc
	 */
	public static boolean isInSymbolicCallChain(MethodInfo methodInfo, StackFrame frame, Config jpfConf) {
		return BytecodeUtils.isClassSymbolic(jpfConf, methodInfo.getClassInfo().getName(), methodInfo, methodInfo.getBaseName())
			|| BytecodeUtils.isMethodSymbolic(jpfConf, methodInfo.getFullName(), methodInfo.getNumberOfArguments(), null)
			|| isInCallStackOfTargetMethod(jpfConf, frame);
	}
	
	public static boolean isInCallStackOfTargetMethod(Config jpfConf, StackFrame frame) {
		String[] methods = jpfConf.getStringArray("symbolic.method");
		List<MethodDesc> symBcDescs = SymExecTreeUtils.convertJPFConfSymbcDescs(methods);
		return SymExecTreeUtils.getTargetMethodOfFrame(symBcDescs, frame) != null;
	}
	
	public static boolean isMethodInfoSymbolicTarget(MethodInfo methInfo, Config jpfConf) {
		MethodDesc mDesc = convertMethodInfo(methInfo);
		String[] methods = jpfConf.getStringArray("symbolic.method");
		List<MethodDesc> symBcDescs = SymExecTreeUtils.convertJPFConfSymbcDescs(methods);
		for(MethodDesc symbTarget : symBcDescs) {
			if(symbTarget.equals(mDesc))
				return true;
		}
		return false;
	}
	
	public static MethodDesc getTargetMethodOfFrame(List<MethodDesc> targetMethods, StackFrame frame) {
		if(frame == null)
			return null;
		StackFrame prevStackFrame = frame;
		while(prevStackFrame != null) {
			MethodDesc mi = SymExecTreeUtils.convertMethodInfo(prevStackFrame.getMethodInfo());
			for(MethodDesc targetMethod : targetMethods) {
				if(targetMethod.equals(mi)) {
					return mi;
				}
			}
			prevStackFrame = prevStackFrame.getPrevious();
		}
		return null;
	}
	
	public static LinkedList<MethodDesc> convertJPFConfSymbcDescs(String[] symbMethodDescs) {
		LinkedList<MethodDesc> symbolicMethods = new LinkedList<MethodDesc>();
		for(String symbcMethod : symbMethodDescs) {
			String shortMethodName = symbcMethod.substring(0, symbcMethod.indexOf("("));
			int argsNum;
			if (symbcMethod.equals(shortMethodName+"()"))
				argsNum = 0;
			else
				argsNum = symbcMethod.split("#").length;
			symbolicMethods.add(new MethodDesc(shortMethodName, argsNum));
		}
		return symbolicMethods;
	}
	
	public static MethodDesc convertMethodInfo(MethodInfo mi) {
		String methodName = mi.getBaseName();
		int argsNum = mi.getNumberOfArguments();
		return new MethodDesc(methodName, argsNum);
	}
}
