package gov.nasa.jpf.symbc;

import gov.nasa.jpf.util.test.TestJPF;
import org.junit.Test;
import java.util.Arrays;

public class TestBooleanSpecial1 extends TestJPF {
       
        static final String INSN_FACTORY = "+vm.insn_factory.class=gov.nasa.jpf.symbc.SymbolicInstructionFactory";
        static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestBooleanSpecial1.testBoolean1(sym#sym)";
        static final String[] JPF_ARGS = { INSN_FACTORY, SYM_METHOD };

	// (x == true)
	private static String B1_PC1 = "# = 1\nx_1_SYMINT != CONST_0 && y_2_SYMINT != CONST_0";
	private static String B1_PC2 = "# = 1\nx_1_SYMINT != CONST_0 && y_2_SYMINT == CONST_0";

	//
	// (x == false)
	private static String B1_PC3 = "x_1_SYMINT == CONST_0 && y_2_SYMINT != CONST_0";
	private static String B1_PC4 = "x_1_SYMINT == CONST_0 && y_2_SYMINT == CONST_0";

	//
	// (y == false)
	private static String B1_PC5 = "y_2_SYMINT == CONST_0";

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

	private void testBoolean1(boolean x, boolean y) {
		String pc = "";
		// Note: "!y" compiles to IFEQ, so it creates a choice generator
		boolean z = !y;

		if (x) {
			assert pcMatches(B1_PC1, pc) || pcMatches(B1_PC2, pc) : 
				makePCAssertString("TestBooleanSpecial1.testBoolean1 if (x == true)", 
						"one of\n" + B1_PC1 + "\nor\n"
						+ B1_PC2, TestUtils
					.getPathCondition());
			z = y;
		} else {
			assert pcMatches(B1_PC3, pc) || pcMatches(B1_PC4, pc) : makePCAssertString("TestBooleanSpecial1.testBoolean1 (x == false)", 
					"one of\n" + B1_PC3 + "\nor\n"
					+ B1_PC4, TestUtils
					.getPathCondition());
		}
		pc = trimPC(TestUtils.getPathCondition());
		if (! z) {
			assert (pcMatches(B1_PC5, pc) || pcMatches(pc, "")) : makePCAssertString(
					"TestBooleanSpecial1.testBoolean1 (z == false)", "one of\n" + (B1_PC5 + " && " + pc) + "\nor\n"
							+ pc, TestUtils.getPathCondition());
			z = true;
		} else {
			assert (pcMatches(pc, "")) : makePCAssertString(
					"TestBooleanSpecial1.testBoolean1 (z == true)",  pc, TestUtils.getPathCondition());
		}
		pc = trimPC(TestUtils.getPathCondition());
	}

	/**
	 * @param args
	 */
        @Test
	public void mainTest () {
		//System.out.println("MAIN: " + Arrays.asList(args));
                if(verifyNoPropertyViolation(JPF_ARGS)) {
		      TestBooleanSpecial1 test = new TestBooleanSpecial1();
		      test.testBoolean1(true, false);
                }
	}

	 public static void main(String[] args) {
                 runTestsOfThisClass(args);
        }
}
