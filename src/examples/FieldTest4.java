public class FieldTest4 extends TestRegionBaseClass {

    int testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return fieldTest4(in0);
    }

    int count = 0;

    public int fieldTest4(int x) {
        count = 0;
        if ( x > 0) {
            if ( x == 1 ) count += 1;
            else if (x == 2) count += 2;
            count = 3;
        } else if ( x < 0 ) count = -1;
//        assert x > 0 ? count == 3 : ( x < 0 ? count == -1 : count == 0);
        return count;
    }

    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        FieldTest4 s = new FieldTest4();
        t.runTest(s);
    }
}

