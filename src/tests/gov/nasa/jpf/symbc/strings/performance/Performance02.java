package gov.nasa.jpf.symbc.strings.performance;

public class Performance02 {
	private static final int MAX_LENGTH = 5;
	
	public static void main (String [] args) {
		test3 (" ", -1,-1,-1);
	}
	
	public static void test (String a, int i) {
		if (i > -1) {
			if (a.indexOf("a") == i) {
				System.out.println("Step 1");
			}
			System.out.println("Step 2");
		}
	}
	
	public static void test2 (String a, int i, int j) {
		if (a.length() < 5 && i > -1 && j > -1) {
			if (a.indexOf("a") == i) {
				if (a.indexOf("b", i) == j) {
					System.out.println("Step 1");
				}
				System.out.println("Step 2");
			}
		}
		System.out.println("Step 3");
	}
	
	public static void test3 (String a, int i, int j, int k) {
		if (a.length() < 15 && i > -1 && j > -1 && k > -1) {
			if (a.indexOf("a") == i) {
				if (a.indexOf("b", i) == j) {
					if (a.indexOf("c", j) == k) {
						System.out.println("Step 1");
						//throw new RuntimeException ("here");
					}
					System.out.println("Step 2");
				}
				System.out.println("Step 3");
			}
		}
		System.out.println("Step 4");
	}
}
