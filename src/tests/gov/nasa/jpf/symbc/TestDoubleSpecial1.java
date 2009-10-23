package gov.nasa.jpf.symbc;

import java.util.Arrays;

public class TestDoubleSpecial1 {
	// x > 1.1
	private static String PC1 = "# = 1\nx_1_SYMREAL > CONST_1.1";

	//
	// (x <= 1.1)
	private static String PC2 = "x_1_SYMREAL < CONST_1.1";

	private static String PC3 = "CONST_1.1 == x_1_SYMREAL";

	//
	// [(x > 1.1) && ((z := y) > 30.0)] || [(x < 1.1) && ((z := x+y) > 30.0)] || [(x == 1.1) && ((z := x+y) > 30.0)]
	private static String PC4 = "(x_1_SYMREAL + y_2_SYMREAL) > CONST_30.0";

	private static String PC5 = "y_2_SYMREAL > CONST_30.0";

	//
	// [((z := x+y) < 30.0) && (x == 1.1)] || [(x < 1.1) && ((z := x+y) < 30.0)] ||
	// [(x < 1.1) && ((z := x+y) == 30.0)] || [(x == 1.1) && ((z := x+y) == 30.0)] ||
	// [(x > 1.1) && ((z := y) < 30.0)] || [(x > 1.1) && ((z := y) == 30.0)]

	private static String PC6 = "CONST_30.0 == (x_1_SYMREAL + y_2_SYMREAL)";

	private static String PC7 = "(x_1_SYMREAL + y_2_SYMREAL) < CONST_30.0";

	private static String PC8 = "y_2_SYMREAL < CONST_30.0";

	private static String PC9 = "CONST_30.0 == y_2_SYMREAL";

	private static String makePCAssertString(String location, String goodPC, String badPC) {
		return String.format("Bad Path condition in %s:\nEXPECTED:\n%s\nACTUAL:\n%s\n", location, goodPC, badPC);
	}

	private static String trimPC(String pc) {
		return pc.substring(pc.indexOf("\n") + 1);
	}

	// Check whether the current PatchPathcondition looks like "# = 1\n <newPC> && <oldPC>"
	private static boolean pcMatches(String newPC, String oldPC) {
		// The current PathCondition with the initial "# = 1\n" removed.
		String currentPC = TestUtils.getPathCondition();
		currentPC = trimPC(currentPC);
		newPC = trimPC(newPC);
		oldPC = trimPC(oldPC);
		if (oldPC.equals(""))
			return newPC.equals(currentPC);
		else
			return (newPC + " && " + oldPC).equals(currentPC);
	}

	// "private" forces calls to use INVOKESPECIAL
	private void testDouble1(double x, double y) {
		String pc = "";
		double z = x + y;

		if (x > 1.1) {
			assert pcMatches(PC1, pc) : makePCAssertString("TestDoubleSpecial1.testDouble1 if x > 1.1", PC1, TestUtils
					.getPathCondition());
			z = y;
		} else {
			assert (pcMatches(PC2, pc) || pcMatches(PC3, pc)) : makePCAssertString("TestDoubleSpecial1.testDouble1 x <= 1.1",
					"either\n" + PC2 + "\nor\n" + PC3, TestUtils.getPathCondition());
		}
		pc = trimPC(TestUtils.getPathCondition());
		if (z > 30.0) {
			assert (pcMatches(PC4, pc) || pcMatches(PC5, pc)) : makePCAssertString(
					"TestDoubleSpecial1.testDouble1 z <= 30.0", "one of\n" + (PC4 + " && " + pc) + "\nor\n"
							+ (PC5 + " && " + pc), TestUtils.getPathCondition());
			z = 91.0;
		} else {
			assert (pcMatches(PC6, pc) || pcMatches(PC7, pc) || pcMatches(PC8, pc) || pcMatches(PC9, pc)) : makePCAssertString(
					"TestDoubleSpecial1.testDouble1 z <= 30.0", "one of\n" + (PC6 + " && " + pc) + "\nor\n"
							+ (PC7 + " && " + pc) + "\nor\n" + (PC8 + " && " + pc) + "\nor\n" + (PC9 + " && " + pc),
					TestUtils.getPathCondition());
		}
		pc = trimPC(TestUtils.getPathCondition());
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		System.out.println("MAIN: " + Arrays.asList(args));
		
		TestDoubleSpecial1 test = new TestDoubleSpecial1();
		
			test.testDouble1(11.0, 21.0);
	}
}
