public class HigherOrder2 extends TestRegionBaseClass {
    int testFunction(int in0) {
        return simpleRegion(in0);
    }
    public static int staticMethod2(int x) {
        int myCount = 0;
        if (x != 100) {
            myCount = 1;
        } else {
            myCount = 3;
        }
        return myCount;
    }
    public static int staticMethod1(int x) {
        int myCount = 0;
        if (x != 10) {
            myCount = staticMethod2(x);
        } else {
            myCount = 2;
        }
        return myCount;
    }



    public int simpleRegion(int x) {
        int val = -1;
        if (x != 0)
            val = staticMethod1(x );
        return val;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        HigherOrder2 h = new HigherOrder2();
        t.runTest(h);
    }
}