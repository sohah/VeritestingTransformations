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

package gov.nasa.jpf.symbc;

public class DoubleTest extends InvokeTest {

  // x > 1.1
  protected static String PC1 ;//= "x > CONST_1.1";
  
  // (x <= 1.1)

  protected static String PC2;// = "x < CONST_1.1";
  protected static String PC3;// = "CONST_1.1 = x";
  
  // [(x > 1.1) && ((z := y) > 30.0)] || [(x < 1.1) && ((z := x+y) > 30.0)] || [(x == 1.1) && ((z := x+y) > 30.0)]
  protected static String PC4;// = "(x + y) > CONST_30.0";
  protected static String PC5 ;//= "y > CONST_30.0";
  
  // [((z := x+y) < 30.0) && (x == 1.1)] || [(x < 1.1) && ((z := x+y) < 30.0)] ||
  // [(x < 1.1) && ((z := x+y) == 30.0)] || [(x == 1.1) && ((z := x+y) == 30.0)] ||
  // [(x > 1.1) && ((z := y) < 30.0)] || [(x > 1.1) && ((z := y) == 30.0)]
  protected static String PC6;// = "CONST_30.0 = (x + y)";
  protected static String PC7;// = "(x + y) < CONST_30.0";
  protected static String PC8;// = "y < CONST_30.0";
  protected static String PC9;// = "CONST_30.0 = y";

  protected static void testDouble(double x, double y) {
    double z = x + y;
    PC1 = TestPC.doublePC1("x",">",1.1);
    PC2 = TestPC.doublePC1("x","<",1.1);
    PC3 = TestPC.doublePC2(1.1,"=","x");
    PC4 = TestPC.doublePC3("x","+","y",">",30.0);
    PC5 = TestPC.doublePC1("y",">",30.0);
    PC6 = TestPC.doublePC4(30.0,"x","+","y","=");
    PC7 = TestPC.doublePC3("x","+","y","<",30.0);
    PC8 = TestPC.doublePC1("y","<",30.0);
    PC9 = TestPC.doublePC2(30.0,"=","y");
    
  
    if (x > 1.1) {
      assert pcMatches(PC1) : makePCAssertString("TestDoubleSpecial1.testDouble1 if x > 1.1", PC1, TestUtils.getPathCondition());
      z = y;
    } else {
      assert (pcMatches(PC2) || pcMatches(PC3)) : makePCAssertString("TestDoubleSpecial1.testDouble1 x <= 1.1",
              "either\n" + PC2 + "\nor\n" + PC3, TestUtils.getPathCondition());
    }
    String pc = TestUtils.getPathCondition();
    if (z > 30.0) {
      assert (pcMatches(joinPC(PC4, pc)) || pcMatches(joinPC(PC5, pc))) : makePCAssertString(
              "TestDoubleSpecial1.testDouble1 z > 30.0", "one of\n" + joinPC(PC4, pc)+ "\nor\n"
              + joinPC(PC5, pc), TestUtils.getPathCondition());
      z = 91.0;
    } else {
      assert (pcMatches(joinPC(PC7,pc)) || pcMatches(joinPC(PC6,pc)) || pcMatches(joinPC(PC8,pc)) 
              ||pcMatches(joinPC(PC9,pc))) : makePCAssertString(
              "TestDoubleSpecial1.testDouble1 z <= 30.0", "one of \n" + joinPC(PC6,pc) + "\nor\n" + 
              joinPC(PC7,pc) + "\nor\n" + joinPC(PC8,pc) + "\nor\n" +joinPC(PC9,pc),
              TestUtils.getPathCondition());
    }
  }
}
