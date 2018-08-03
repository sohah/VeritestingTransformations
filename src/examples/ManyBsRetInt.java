import gov.nasa.jpf.symbc.Debug;

public class ManyBsRetInt {
    public static int countBs(char[] ary) {
	int count = 0;
	for (int i = 0; i < ary.length; i++) {
	    if (ary[i] == 'B')
		count++;
	}
	return count;
    }

    public static int countBs100(char[] ary) {
	int count = 0;
	for (int i = 0; i < 100; i++) {
	    if (ary[i] == 'B')
		count++;
	}
	return count;
    }

    public static int test_countBs100() {
	char[] ary = new char[100];
	for (int i = 0; i < 100; i++) {
	    ary[i] = (char)Debug.makeSymbolicInteger("a" + i);
	}
	return countBs100(ary);
    }

    public static void main(String[] args) {
	char[] ary = new char[5];
	ary[0] = ary[1] = ary[2] = ary[3] = ary[4] = 'a';
	int count = test_countBs100();
	if (count == 75) {
	    System.out.println("Success");
	} else {
	    System.out.println("Failure, count " + count + " != 75");
	}
    }
}
