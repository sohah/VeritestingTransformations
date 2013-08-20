/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.InvokeTest;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestRTDebugSymVar extends InvokeTest {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.realtime.TestRTDebugSymVar.procedure()";
		
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests;${jpf-symbc}/build/classes;${jpf-symbc}/../SARTSBenchmarks/bin;${jpf-symbc}/../scjNoRelativeTime/bin;${jpf-symbc}/../JOP/bin";
	
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.realtime.UppaalTranslationListener";
	//private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.symexectree.visualizer.SymExecTreeVisualizerListener";
	private static final String OUTPUTPATH = "+symbolic.visualiser.basepath = ./";
	
	private static final String REALTIME_PLATFORM = "+symbolic.realtime.platform = jop";
	private static final String TETASARTS = "+symbolic.realtime.targettetasarts = false";
	private static final String REALTIME_PATH = "+symbolic.realtime.outputpath = ${jpf-symbc}/";
	private static final String OPTIMIZE = "+symbolic.realtime.optimize = false";
	
	private static final String SOLVER = "+symbolic.dp=choco";
	
	
	//remember the nosolver option is like a cfg traversal!
	
	//private static final String SOLVER = "+symbolic.dp=no_solver";
	private static final String[] JPF_ARGS = {INSN_FACTORY,
											  OUTPUTPATH,
											  TETASARTS, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD, 
											  OPTIMIZE, 
											  REALTIME_PATH, 
											  REALTIME_PLATFORM,
											  SOLVER};

	
	public static void main(String[] args) {
		TestSimpleSys testInvocation = new TestSimpleSys();
		testInvocation.mainTest();		
	}
	
	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			TestRTDebugSymVar test = new TestRTDebugSymVar();
			test.procedure();
		}
	}
	
	public void procedure() {
		int symVar = Debug.makeSymbolicInteger("NEWSYMVAR");
		if(symVar > 10) {
			callee(symVar);
			callee(symVar);
			callee(symVar);
			callee(symVar);
			callee(symVar);
			callee(symVar);
		} else 
			callee(symVar);
	}
	
	public void callee(int var) {
		var += 10;
	}
}