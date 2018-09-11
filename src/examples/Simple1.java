class Simple1 extends TestRegionBaseClass {
    int testFunction(int in0) {
        return simple_region(in0);
    }
    int simple_region(int x) {
        int count;
        if (x != 0) {
            count = 3;
        } else {
            count = 4;
        }
        return count;
    }
}