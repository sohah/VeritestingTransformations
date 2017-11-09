/*
 * example to demonstrate veritesting
*/

public class VeritestingPerf {

    public static void main(String[] args) {
        (new VeritestingPerf()).countBitsSet(1);
    }

    public int countBitsSet(int x) {
        int count = 0;
        while (x != 0) {
            int lowbit = x & 1;
            int flag;
            if (lowbit != 0) flag = 1;
            else flag = 0;
            count += flag;
            x = x >>> 1; // logical right shift
        }
        return count;
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
