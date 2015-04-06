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

import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.X;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
class InstanceFieldPropagation extends Thread {
	X myX; // initially not set

	public void run() {
		//myX = (X) Debug.makeSymbolicRef("SYMB", myX);
		if(myX != null){
			//System.out.println("T: accessed global myX");
			if (!myX.pass){  // (2) won't fail unless main is between (0) and (1)
				//throw new AssertionError("gotcha");
				System.out.println("Gotcha!");
			}
		}
		Debug.printSymbolicRef(myX, "MyX");
	}    
}
