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
public class TestSimpleSys extends InvokeTest {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.realtime.SimpleSys.computation(sym#sym)";
		
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests;${jpf-symbc}/../SARTSBenchmarks/bin;${jpf-symbc}/../scjNoRelativeTime/bin;${jpf-symbc}/../JOP/bin";
	
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.realtime.UppaalTranslationListener";
	private static final String REALTIME_PLATFORM = "+symbolic.realtime.platform = jop";
	private static final String TETASARTS = "+symbolic.realtime.tetasarts = false";
	private static final String REALTIME_PATH = "+symbolic.realtime.outputpath = ${jpf-symbc}/";
	private static final String OPTIMIZE = "+symbolic.realtime.optimize = true";
	
	
	
	//remember the nosolver option is like a cfg traversal!
	
	//private static final String SOLVER = "+symbolic.dp=no_solver";
	private static final String[] JPF_ARGS = {INSN_FACTORY, 
											  TETASARTS, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD, 
											  OPTIMIZE, 
											  REALTIME_PATH, 
											  REALTIME_PLATFORM};

	
	public static void main(String[] args) {
		TestSimpleSys testInvocation = new TestSimpleSys();
		testInvocation.mainTest();		
	}
	
	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			SimpleSys test = new SimpleSys();
			test.computation(false, true);
		}
	}
}
