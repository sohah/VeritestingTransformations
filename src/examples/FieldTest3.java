public class FieldTest3  extends TestRegionBaseClass {

    int testFunction(int in0, int in1, int in2, int in3, int in4, int in5,
                     boolean b0, boolean b1, boolean b2, boolean b3, boolean b4, boolean b5) {
        return fieldTest3(in0);
    }

    int count = 0;

    public int fieldTest3(int x) {
        count = x;
        if (x != 0) {
            count += 1;
            count += 2;
        }
        else {
            count = 2;
            count += 1;
        }
//        assert (x != 0 ? count == x + 3 : count == 3);
        return count;
    }
    public static void main(String[] args) {
        TestVeritesting t = new TestVeritesting();
        FieldTest3 s = new FieldTest3();
        t.runTest(s);
    }
}

