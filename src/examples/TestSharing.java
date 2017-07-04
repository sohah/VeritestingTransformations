
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

public class TestSharing {
	public static void testSharing(int x) {
    for(int i=0; i<21; i++) x = x + x;
    if ( x < -50 || x > 50) System.out.println("then side");
    else System.out.println("else side");
	}
	
	public static void main(String[] args) {
		testSharing(0);
	}
}
