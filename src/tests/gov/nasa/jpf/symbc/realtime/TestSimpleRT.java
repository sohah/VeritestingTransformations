/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import gov.nasa.jpf.symbc.InvokeTest;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestSimpleRT {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestSimpleRT.computation(sym)";
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.SymbolicListener";//realtime.UppaalTranslationListener";
	//private static final String[] JPF_ARGS = {INSN_FACTORY, LISTENER, SYM_METHOD};
	
	
	public static void main(String[] args) {
		TestSimpleRT testInvocation = new TestSimpleRT();
		testInvocation.computation(true);		
	}
/*	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			TestSimpleRT test = new TestSimpleRT();
			test.computation(false);
		}
	}
	*/
	public int computation(boolean cond) {
		int b = 0;
		if(cond) {
			b = callee(2);
			return b + 2;
		}
		else
			return b;
	}
	
	public int callee(int a) {
		return a + 3;
	}
}
