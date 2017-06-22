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
 * example to demonstrate creation of test suites for path coverage
 */
public class TestPaths {

  public static void main (String[] args){
   // testMe(42, false);
	System.out.println("!!!!!!!!!!!!!!! Start Testing! ");
    (new TestPaths()).testMe3(0,0);
  }

  public static void testMe3 (int x, int y) {
    System.out.println("x = " + x + ", y = " + y);
    int a=0, b=0;
    
    if (x <= 800) a = -1;
    else a = 1;
    if (y <= 1200) b = -1; 
    else b = 1;
    
    System.out.println("a = " + a + ", b = " + b);
  }

  // how many tests do we need to cover all paths?
  public static void testMe (int x, boolean b) {
    System.out.println("x = " + x);
    int y=0;
    if (x <= 1200){
      //System.out.println("  <= 1200");
      y=-1;
    }
    if(x >= 1200){
      //System.out.println("  >= 1200");
      y=1;
    }
  }

  public void testMe2 (int x, boolean b) {
	  System.out.println("!!!!!!!!!!!!!!! First step! ");
	    //System.out.println("x = " + x);
        if (b) {
        	if (x <= 1200){
        		System.out.println("  <= 1200");
        	}
        	if(x >= 1200){
        		System.out.println("  >= 1200");
        	}
        } else System.out.println("  b is false");
  }

}
