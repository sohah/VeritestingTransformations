class Simple1 extends TestRegionBaseClass {
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
        t.runTest(new Simple1());
    }
}