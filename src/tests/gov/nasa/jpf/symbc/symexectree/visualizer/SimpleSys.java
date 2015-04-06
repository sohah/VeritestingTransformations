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


/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SimpleSys {
	
	public static void main(String[] args) {
		SimpleSys s = new SimpleSys();
		s.compAB(2, 2);
	}

	public int compAB(int a, int b) {
		if(a > b) {
			if(a == b) {
				return number() + 42;
			} else
				return 42;
		} else
			return number();
		
		/*int d = 0;
		for(int c = 0; c < a; c++) {
			d += 10;
		}
		if(b > 3) {
			int g = 10;
			if(callee(g) > 2) {
				g++;
			}
		} else {
			d -= 10;
		}*/
	}
	
	public int number() {
		return 24;
	}
}
