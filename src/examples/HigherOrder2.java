public class HigherOrder2 extends TestRegionBaseClass {
    // Classes that wish to test a veritesting region can populate the expected value of
    // VeritestingListener.veritestRegionCount in this variable. TestVeritesting will assert
    // VeritestingListener.veritestRegionCount to be equal to veritestRegionExpectedCount
    // Since on every execution path, we expect a region to be instantiated, this variable should correspond to the
    // total number of execution paths we expect during equivalence-checking.
    // With 3 branches in simpleRegion(), I (vaibhav) expect the region inside simpleRegion() to be instantiated 8 times,
    // once on every execution path through the simpleRegion().
    public int veritestRegionExpectedCount = 8;
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
        // The string prefix in the following println needs to be "veritestRegionExpectedCount = ". This is the string
        // that SPF will be looking for in this program's output to find out this tests's expected value of number of
        // veritesting region instantiations.
        System.out.println("veritestRegionExpectedCount = " + h.veritestRegionExpectedCount);
    }
}