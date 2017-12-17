/*
 * example to demonstrate veritesting
*/


import gov.nasa.jpf.symbc.Debug;

public class VeritestingPerf {

    private int count;

    public static void main(String[] args) {
        //(new VeritestingPerf()).countBitsSet(1);
        int x[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20};
        (new VeritestingPerf()).testMe4(x, 2);
        //(new VeritestingPerf()).arrayTest(x, 6);
    }

    public int countBitsSet(int x) {
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

    public void testMe4 (int[] x, int len) {
        int sum = 0; //Debug.makeSymbolicInteger("sum");
        for(int i=0; i < len; i++)
            x[i] = Debug.makeSymbolicInteger("x"+i);
        for (int i = 0; i < len; i++) {
            if (x[i] < 0) sum += -1;
            else sum += 1;
        }
        if (sum < 0) System.out.println("neg");
        else if (sum > 0) System.out.println("pos");
        else System.out.println("bug");
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
