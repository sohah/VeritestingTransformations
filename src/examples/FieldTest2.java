public class FieldTest2 extends TestRegionBaseClass {

    int testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return fieldTest2(in0);
    }

    int count = 0;

    public int fieldTest2(int x) {
        if (x != 0) count = 1;
        else count = 2;
//        assert( x != 0 ? count == 1 : count == 2);
        return count;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        FieldTest2 s = new FieldTest2();
        t.runTest(s);
    }
}

