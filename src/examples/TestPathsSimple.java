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
 * modified for veritesting
 */

import gov.nasa.jpf.symbc.Debug;

public class TestPathsSimple {

  public static void main (String[] args){
   //testMe(42, false);
  System.out.println("!!!!!!!!!!!!!!! Start Testing! ");
  //(new TestPathsSimple()).testMe3(0,0,0);
  }
/*
  public int testMe4(int x, int y, int z) {
    if (x > y) {
      return x;
    }
    else {
      y = z;
    }
    return z;
  }

  public void testMe3 (int x, int y, int z) {
    System.out.println("x = " + x + ", y = " + y);
    // int a_final = Debug.makeSymbolicInteger("a_final");
    // int b_final = Debug.makeSymbolicInteger("b_final");
    int a=11, b=12;

    // Begin region for static unrolling
    if (x <= 800 ) a = -1;
    else a = 1;
    if (y <= 1200 ) b = -1;
    else b = 1;
    // End region for static unrolling
  
    if (a == -1) System.out.println("a = -1");
    else if (a == 1) System.out.println("a = 1");
    else System.out.println("a != 1 && a != -1");
    if(b == -1) System.out.println("b = -1");
    else if (b == 1) System.out.println("b = 1");
    else System.out.println("b != 1 && b != 1");
    System.out.println("-x-x-x-x-");
  }
*/
  // how many tests do we need to cover all paths?
 public static int testMe (int x, boolean b) {
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
    return y;
  }

  public static int mwwNestedIfBranch(int x, int y) {
    if (x < y) {
      if (y < 100) {
        y = 100;
      } else {
        y = y * 2;
      }
    } else {
      y = x;
    }
    return y;
  }

  public static int mwwNestedIfBranchTrailingStmt(int x, int y) {
    if (x < y) {
      if (y < 100) {
        y = 100;
      } else {
        y = y * 2;
      }
      y += 4;
    } else {
      y = x;
    }
    return y;
  }

  public static int mwwNestedIfBranchEarlyReturn1(int x, int y) {
    if (x < y) {
      if (y < 100) {
        return y;
      } else {
        y = y * 2;
      }
      y += 4;
    } else {
      y = x;
    }
    return y;
  }

  public static int mwwNestedIfBranchEarlyReturn2(int x, int y) {
    if (x < y) {
      if (y < 100) {
        y = 100;
      } else {
        return y;
      }
      y += 4;
    } else {
      y = x;
    }
    return y;
  }

  public static int mwwNestedElseBranch(int x, int y) {
    if (x < y) {
      y = x;
    } else {
      if (y < 100) {
        y = 100;
      } else {
        y = y * 2;
      }
    }
    return y;
  }

  public static int mwwNestedElseBranchTrailingStmt(int x, int y) {
    if (x < y) {
      y = x;
    } else {
      if (y < 100) {
        y = 100;
      } else {
        y = y * 2;
      }
      y += 2;
    }
    return y;
  }

  public static int mwwIfEarlyReturn(int x, int y) {
    if (x < y) {
      y += 2;
      return y;
    } else {
      y *= 2;
    }
    return y;
  }

  public static int mwwElseEarlyReturn(int x, int y) {
    if (x < y) {
      y *= 2;
    } else {
      y += 2;
      return y;
    }
    return y;
  }

  public static int mwwNestedElseBranchEarlyReturn1(int x, int y) {
    if (x < y) {
      y = x;
    } else {
      if (y < 100) {
        return y;
      } else {
        y = y * 2;
      }
      y += 2;
    }
    return y;
  }

  public static int mwwNestedElseBranchEarlyReturn2(int x, int y) {
    if (x < y) {
      y = x;
    } else {
      if (y < 100) {
        return y;
      } else {
        y = y * 2;
      }
      y += 2;
    }
    return y;
  }


  /*
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
*/
}
