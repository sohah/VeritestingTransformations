/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.symbc.InvokeTest;
import gov.nasa.jpf.symbc.realtime.SimpleSys;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestConcurrentVisualization extends InvokeTest {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.symexectree.visualizer.TestConcurrentVisualization$ConcCompute.run()";
	
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests;${jpf-symbc}/../SARTSBenchmarks/bin;${jpf-symbc}/../scjNoRelativeTime/bin;${jpf-symbc}/../JOP/bin";
	
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.symexectree.visualizer.SymExecTreeVisualizerListener";
	private static final String OUTPUTPATH = "+symbolic.visualiser.basepath = ./";
	private static final String FORMAT = "+symbolic.visualiser.outputformat = pdf";
	
	
	
	//remember the nosolver option is like a cfg traversal!
	
	//private static final String SOLVER = "+symbolic.dp=no_solver";
	private static final String[] JPF_ARGS = {INSN_FACTORY, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD,
											  OUTPUTPATH,
											  FORMAT
											  };

	
	/*public static void main(String[] args) {
		TestConcurrentVisualization testInvocation = new TestConcurrentVisualization();
		testInvocation.mainTest();		
	}*/
	
	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			Thread t1 = new Thread(new ConcCompute());
			Thread t2 = new Thread(new ConcCompute());
			
			t1.start();
			t2.start();
		}
	}
	private static boolean cond = false;
	
	private class ConcCompute implements Runnable {

		@Override
		public void run() {
			if(TestConcurrentVisualization.cond) {
				this.computation(1,3);
			} else {
				TestConcurrentVisualization.cond = true;
			}
			
		}
		
		private int computation(int a, int b) {
			return a +b+a+b+b+b+b+b+b;
		}
		
	}
}
