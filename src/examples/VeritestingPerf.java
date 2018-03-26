/*
 * example to demonstrate veritesting
*/


import gov.nasa.jpf.symbc.Debug;
import sun.reflect.annotation.ExceptionProxy;

import java.util.ArrayList;

public class VeritestingPerf {

    public int count = 0;

    public static void main(String[] args) {
        //(new VeritestingPerf()).cfgTest(1);
        (new VeritestingPerf()).countBitsSet(1);
        int x[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20};
//        (new VeritestingPerf()).inRangeloadArrayTC( 22, 10);


//        (new VeritestingPerf()).outRangeloadArrayTC( 2, 10);
 //       (new VeritestingPerf()).outRangeConcreteTC( 20, 10);
        //(new VeritestingPerf()).testMe5(x, 1);
        //(new VeritestingPerf()).testMe6(x, 12, -1, 1);
        //(new VeritestingPerf()).testMe4(x, 12, -1, 1);
 //       (new VeritestingPerf()).arrayTest(x, 6);
        //(new VeritestingPerf()).checkOperator();
//        ArrayList<Integer> list = new ArrayList<>();
//        list.add(Debug.makeSymbolicInteger("a1"));
//        list.add(Debug.makeSymbolicInteger("a2"));
//        (new VeritestingPerf()).countArrayList(list);
    }

    public int countBitsSetSimple(int x) {
        //int count = 0;
        while (x != 0) {
            int lowbit = x & 1;
            int flag;// = 0;
            if (lowbit != 0) flag = 1;
            else flag = 0;
            count += flag;
            x = x >>> 1; // logical right shift
        }
        return count;
    }

    public int countBitsSet(int x) {
        TempClass tempClass = new TempClassDerived();
        count = 1;
        //TempClass tempClass = new TempClass();
        while (x != 0) {
            if ((x & 1) != 0) {
                // nested field access test case 1
                //count += tempClass.tempClass2.tempInt2;
                //nested field access test case 2
                //TempClass2 tempClass2 = tempClass.tempClass2;
                //tempClass2.tempInt2 += count;
                //tempClass.tempInt = 1; //creates r/w interference with tempClass.getOne's method summary
                count += tempClass.getOne(0);
                //count += tempClass.myInt; //use this to test dynamic field access
            }
            x = x >>> 1; // logical right shift
        }
        return count;
    }

    //testing inRangeArrayLoad for symbolic & concrete index
    public int inRangeloadArrayTC(int index, int length)  {
        int[] x = {1,2,3,4,5,6,7,8};
        int temp = 0;
        int y = 1;
        if(length>0)
             temp = x[index];
        else
            temp =1;
        return temp;
    }

    //testing outRangeArrayLoad for symbolic index
    public int outRangeloadArrayTC(int index, int length) throws ArrayIndexOutOfBoundsException {
        int[] x = {1,2,3,4,5,6,7,8};
        int temp = 0;
        int y = 1;
        if(length>0)
            temp = x[index];
        else
            temp =1;
        return temp;
    }

    //testing outOfRange for concrete Index
    public int outRangeConcreteTC(int index, int length) throws ArrayIndexOutOfBoundsException{
        int[] x = {1,2,3,4,5,6,7,8};
        int temp = 0;
        int y = 1;
        if(length>0)
            temp = x[index];
        else
            temp =1;
        return temp;
    }

    public int countArrayList(ArrayList<Integer> x) {
        // x = ArrayList of symbolic integers with
        // concrete length
        int sum = 0;
        for (int i = 0; i < x.size(); i++) {
            // Begin region for static unrolling
            if (x.get(i) < 0) sum += -1;
            else if (x.get(i) > 0) sum += 1;
            // End region for static unrolling
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
        return sum;
    }

    static int a, b, c, d, e, f;
    public int checkOperator() {
        int ret = -1;
        a = Debug.makeSymbolicInteger("a");
        b = Debug.makeSymbolicInteger("b");
        if(a < b) ret = 1;
        else ret = 0;
        return ret;
    }

    public int cfgTest(int x) {
        int ret = 0;
        while(x >= 0) {
            x--;
            if (x == 0) ret = 1;
            else ret = -1;
            x = x - 1;
        }
        return ret;
    }

    public void testMe4 (int[] x, int len, int minusOne, int plusOne) {
        int sum = 0; //Debug.makeSymbolicInteger("sum");
        int temp = 2;
        for(int i=0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x"+i);
        for (int i = 0; i < len; i++) {
            if (x[i] < 0) {
                int temp2 = x[0];
                temp = minusOne;
                sum += temp;
            }
            else {
                temp = plusOne;
                sum += temp;
            }
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
    }

    public void testMe5 (int[] x, int len) {
        int sum = 0; //Debug.makeSymbolicInteger("sum");
        for(int i=0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x"+i);
        for (int i = 0; i < len; i++) {
            int val = x[i];
            if (val < 0) sum += -1;
            else if(val > 0) sum += 1;
            else sum += 0;
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
    }

    public int testMe6 (int[] x, int len, int minusOne, int plusOne) {
//        int sum = 0; //Debug.makeSymbolicInteger("sum");
//        int temp = 2;
//        for(int i=0; i < len; i++)
//            x[i] = Debug.makeSymbolicInteger("x"+i);
//        int temp2 =0;
//        for (int i = 0; i < len; i++) {
//            if (len < 0) {
//                temp2 = x[minusOne];
//                temp = minusOne;
//                sum += temp;
//            }
//            else {
//                x[0] = 0;
//                temp = plusOne;
//                sum += temp;
//            }
//        }
//        if (sum < 0) {System.out.println("neg"); temp2=x[minusOne];}
//        else if (sum > 0) System.out.println("pos");
//        else System.out.println("bug");
        return 1;
    }
    public void arrayTest (int[] x, int len) {
        for(int i=0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x"+i);
        for (int i = 0; i < len; i++) {
            if (x[i] < 0) x[i] *= -1;
            else x[i] *= 2;
        }
    }
};

class TempClassDerived extends TempClass {

    public int tempInt = 1; //change this to 2 to test read after write on a class field inside a Veritesting region

    public int myInt = 1;

    public int getTempInt(int a) {
        //TempClass2 t = new TempClass2();
//        t.tempMethod();
        return tempInt;
    }

    public int getOne(int a) {
        /*tempInt = a + 1; //LOCAL_INPUT,  FIELD_OUTPUT holes
        a = tempInt + 2; //LOCAL_OUTPUT, FIELD_INPUT holes
        tempInt = a + 3; //LOCAL_INPUT,  FIELD_INPUT holes
*/
        //VeritestingPerf.count += 1;
        //return tempInt;
        return getTempInt(a);
    }
}

class TempClass {

    public int tempInt = 1;

    public int myInt = 0;

    public TempClass() {
        this.tempClass2 = new TempClass2();
    }

    public int getTempInt() { return tempInt; }

    public int getOne(int a) { tempInt = a; return tempInt; }

    TempClass2 tempClass2;
}

class TempClass2 {

    public int tempInt2 = 1;

    public int tempMethod() { return 0;}
}























/*
  public void collatz(int n) {
    int inter;
    while(n != 1) {
      if( (n & 1) == 1) {
        inter = 3*n + 1;
      } else {
        inter = (n >> 1);
      }
      n = inter;
    }
  }

  public void testMe4 (int[] x, int len) {
    int sum = 0; //Debug.makeSymbolicInteger("sum");
    // for(int i=0; i < len; i++) 
    //   x[i] = Debug.makeSymbolicInteger("x"+i);
    for (int i=0; i < len; i++) {
      if (x[i] < 0) sum += -1;
      else if (x[i] > 0) sum += 1;
    }
    if (sum < 0) System.out.println("neg");
    else if (sum > 0) System.out.println("pos");
    else System.out.println("bug");
  }

  public int gcd(int a, int b) {
    while( a != b ) {
      if ( a > b ) a = a - b;
      else b = b - a;
    }
    return a;
  }



  public int oneBranch(int x) {
    int sum=0;
    if(x < 0) sum += -1;
    else sum += 1;
	return sum;
  }

}*/
