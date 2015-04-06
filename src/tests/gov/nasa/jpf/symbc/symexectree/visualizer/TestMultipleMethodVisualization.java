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
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.symbc.InvokeTest;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestMultipleMethodVisualization extends InvokeTest {

private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.symexectree.visualizer.TestMultipleMethodVisualization$TestMultipleMethods.compAB(sym#sym);gov.nasa.jpf.symbc.symexectree.visualizer.TestMultipleMethodVisualization$TestMultipleMethods.number(sym)";
	
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests;";
	
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.symexectree.visualizer.SymExecTreeVisualizerListener";
	private static final String OUTPUTPATH = "+symbolic.visualizer.basepath = ${jpf-symbc}/prettyprint/";
	private static final String FORMAT = "+symbolic.visualizer.outputformat = pdf";
	
	private static final String SOLVER = "+symbolic.dp=choco";
	private static final String[] JPF_ARGS = {INSN_FACTORY, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD,
											  OUTPUTPATH,
											  FORMAT,
											  SOLVER
											  };

	
	public static void main(String[] args) {
		TestPrintSimpleSys testInvocation = new TestPrintSimpleSys();
		testInvocation.mainTest();		
	}
	
	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			TestMultipleMethods test = new TestMultipleMethods();
			test.compAB(1,2);
		}
	}
	
	private class TestMultipleMethods {

		public int compAB(int a, int b) {
			if(a > b) {
				if(a == b) {
					return number(2) + 42;
				} else
					return 42;
			} else
				return number(1);
		}
		
		public int number(int i) {
			if(i > 100) {
				return i + 10;
			} else {
				for(int a = 0; a < 2; a++) {
					i++;
				}
				return i;
			}
		}
	}
}

