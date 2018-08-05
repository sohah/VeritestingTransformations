import gov.nasa.jpf.symbc.Debug;

public class ManyBs {
    public static boolean countBs(char[] ary) {
	int count = 0;
	for (int i = 0; i < ary.length; i++) {
	    if (ary[i] == 'B')
		count++;
	}
	if (count == 75)
	    return true;
	else
	    return false;
    }

    public static boolean countBs100(char[] ary) {
	int count = 0;
	for (int i = 0; i < 100; i++) {
	    if (ary[i] == 'B')
		count++;
	}
	if (count == 75)
	    return true;
	else
	    return false;
    }

    public static boolean test_countBs100() {
	char[] ary = new char[100];
	for (int i = 0; i < 100; i++) {
	    ary[i] = (char)Debug.makeSymbolicInteger("a" + i);
	}
	return countBs100(ary);
    }

    public static void main(String[] args) {
	char[] ary = new char[5];
	ary[0] = ary[1] = ary[2] = ary[3] = ary[4] = 'a';
	if (test_countBs100()) {
	    System.out.println("Success");
	} else {
	    System.out.println("Failure");
	}
    }
}
