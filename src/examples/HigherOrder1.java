
public class HigherOrder1 extends TestRegionBaseClass {
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

    public static int simpleRegion(int y) {
        int methodCount = 0;
        if (y != 100)
            methodCount = staticMethod1(y);
        return methodCount;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        HigherOrder1 h = new HigherOrder1();
        t.runTest(h);
    }
}