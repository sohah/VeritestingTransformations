package gov.nasa.jpf.symbc;

import java.util.Arrays;

public class TestFloatStatic1 {
	// x > 1.1f
	private static String PC1 = "# = 1\nx_1_SYMREAL > CONST_1.100000023841858";

	//
	// (x <= 1.1f)
	private static String PC2 = "x_1_SYMREAL < CONST_1.100000023841858";

	private static String PC3 = "CONST_1.100000023841858 == x_1_SYMREAL";

	//
	// [(x > 1.1f) && ((z := y) > 30.0f)] || [(x < 1.1f) && ((z := x+y) > 30.0f)] || [(x == 1.1f) && ((z := x+y) > 30.0f)]
	private static String PC4 = "(x_1_SYMREAL + y_2_SYMREAL) > CONST_30.0";

	private static String PC5 = "y_2_SYMREAL > CONST_30.0";

	//
	// [((z := x+y) < 30.0f) && (x == 1.1f)] || [(x < 1.1f) && ((z := x+y) < 30.0f)] ||
	// [(x < 1.1f) && ((z := x+y) == 30.0f)] || [(x == 1.1f) && ((z := x+y) == 30.0f)] ||
	// [(x > 1.1f) && ((z := y) < 30.0f)] || [(x > 1.1f) && ((z := y) == 30.0f)]

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

	public static void testFloat1(float x, float y) {
		String pc = "";
		float z = x + y;

		if (x > 1.1f) {
			assert pcMatches(PC1, pc) : makePCAssertString("TestFloatStatic1.testFloat1 if x > 1.1f", PC1, TestUtils
					.getPathCondition());
			z = y;
		} else {
			assert (pcMatches(PC2, pc) || pcMatches(PC3, pc)) : makePCAssertString(
					"TestFloatStatic1.testFloat1 x <= 1.1f", "either\n" + PC2 + "\nor\n" + PC3, TestUtils
							.getPathCondition());
		}
		pc = trimPC(TestUtils.getPathCondition());
		if (z > 30.0f) {
			assert (pcMatches(PC4, pc) || pcMatches(PC5, pc)) : makePCAssertString(
					"TestFloatStatic1.testFloat1 z <= 30.0f", "one of\n" + (PC4 + " && " + pc) + "\nor\n"
							+ (PC5 + " && " + pc), TestUtils.getPathCondition());
			z = 91.0f;
		} else {
			assert (pcMatches(PC6, pc) || pcMatches(PC7, pc) || pcMatches(PC8, pc) || pcMatches(PC9, pc)) : makePCAssertString(
					"TestFloatStatic1.testFloat1 z <= 30.0f", "one of\n" + (PC6 + " && " + pc) + "\nor\n"
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

		testFloat1(11.0f, 21.0f);
	}
}
