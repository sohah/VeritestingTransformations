package gov.nasa.jpf.symbc;


public class TestSwitch {
	public enum Y {Y1, Y2};
	
	void testSwitch1() {
		Y y = Y.Y1;
//		int x = 1;
//
//		switch (x) {
//		case 1: System.out.println(1); break;
//		case 2: System.out.println(2); break;
//		default: System.out.println("default: "); break;
//		}
		switch (y) {
//		case Y1: System.out.println(1); break;
		case Y2: System.out.println(2); break;
		default: System.out.println("default: "); break;
		}
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		TestSwitch test = new TestSwitch();

		test.testSwitch1();
	}
}
