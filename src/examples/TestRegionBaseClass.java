public class TestRegionBaseClass {
    // Classes that wish to test a veritesting region should put the region inside a method and call it from a
    // overridden testFunction
    int testFunction(int x){return 0;}

    // Classes that wish to test a veritesting region can populate the expected value of
    // VeritestingListener.veritestRegionCount in this variable. TestVeritesting will assert
    // VeritestingListener.veritestRegionCount to be equal to veritestRegionExpectedCount
    // Since on every execution path, we expect a region to be instantiated, this variable should correspond to the
    // total number of execution paths we expect during equivalence-checking.
    int veritestRegionExpectedCount = -1;
}