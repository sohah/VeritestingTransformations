/**
 * 
 */
package gov.nasa.jpf.symbc;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestLCMPLConditions extends InvokeTest {

	  private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.TestLCMPLConditions.twoConditions(sym#sym);gov.nasa.jpf.symbc.TestLongConditions.threeConditions(sym#sym)";
	  //private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.SymbolicListener";
	  private static final String DEBUG = "+symbolic.debug=true";	  
	  private static final String DP = "+symbolic.dp=coral";	 
	  private static final String[] JPF_ARGS = {INSN_FACTORY, SYM_METHOD, DEBUG, DP};

	  public static void main(String[] args) {
	    runTestsOfThisClass(args);
	  }

	  @Test
	  public void mainTest() {
	    if (verifyNoPropertyViolation(JPF_ARGS)) {
	    	twoConditions(20000000000L, 20000000000L);
	    	//threeConditions(20000000000L, 20000000000L);
	    }
	  }
	  
	  public static void twoConditions(long a, long b) {
		 if(a >= 1) { //try with 50L here 
			 // if(a >= 2) { //try with 51L here (add one discrete value to the previous)
			//	 long c = a + b;
			 // }
		 }

	  }
	  
	  public static long threeConditions(long a, long b) {
		  long c = 10L;
		  if(a > b) {
			  c = 500L;
		  }
		  else if(b > a) {
			  c = 7000L;
		  }
		  else if(b == a) {
			  c = 1000L;
		  }
		  return c;		  
	  }
}
