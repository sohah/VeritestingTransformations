
class Simple1 extends TestRegionBaseClass {
    // Classes that wish to test a veritesting region can populate the expected value of
    // VeritestingListener.veritestRegionCount in this variable. TestVeritesting will assert
    // VeritestingListener.veritestRegionCount to be equal to veritestRegionExpectedCount
    // Since on every execution path, we expect a region to be instantiated, this variable should correspond to the
    // total number of execution paths we expect during equivalence-checking.
    // With 1 branch in simpleRegion(), I (vaibhav) expect the region inside simpleRegion() to be instantiated 2 times,
    // once on every execution path through the simpleRegion().
    public int veritestRegionExpectedCount = 2;
    int testFunction(int in0) {
        return simpleRegion(in0);
    }
    int simpleRegion(int x) {
        int count;
        if (x != 0) {
            count = 3;
        } else {
            count = 4;
        }
        return count;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        Simple1 s = new Simple1();
        t.runTest(s);
        // The string prefix in the following println needs to be "veritestRegionExpectedCount = ". This is the string
        // that SPF will be looking for in this program's output to find out this tests's expected value of number of
        // veritesting region instantiations.
        System.out.println("veritestRegionExpectedCount = " + s.veritestRegionExpectedCount);
    }
}