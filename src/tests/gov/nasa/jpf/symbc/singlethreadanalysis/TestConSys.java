/**
 * 
 */
package gov.nasa.jpf.symbc.singlethreadanalysis;

import gov.nasa.jpf.symbc.Debug;
import gov.nasa.jpf.symbc.InvokeTest;
import gov.nasa.jpf.symbc.realtime.SimpleSys;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestConSys extends InvokeTest {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.singlethreadanalysis.TestConSys$ConcCompute.run()";
	
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests;${jpf-symbc}/../SARTSBenchmarks/bin;${jpf-symbc}/../scjNoRelativeTime/bin;${jpf-symbc}/../JOP/bin";
	
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.symexectree.visualizer.SymExecTreeVisualizerListener";
	//private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.singlethreadanalysis.SingleThreadListener";
	private static final String OUTPUTPATH = "+symbolic.visualizer.basepath = ./prettyprint";
	private static final String FORMAT = "+symbolic.visualizer.outputformat = pdf";
	private static final String DEBUG = "+symbolic.debug = true";

	private static final String[] JPF_ARGS = {INSN_FACTORY, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD,
											  OUTPUTPATH,
											  FORMAT,
											  DEBUG
											  };

	
	public static void main(String[] args) {
		ConcCompute conc = new ConcCompute();
		
		Thread t1 = new Thread(conc);
		Thread t2 = new Thread(new Racer(conc));
		t1.start();
		System.out.println("Main executing. before");
		//conc.setcond(true);
		System.out.println("Main executing. after");
		t2.start();
	}
	
	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			TestConSys.main(null);
		}
	}
	private static int id = 0;
	static class ConcCompute implements Runnable {
		public boolean cond = false;//Debug.makeSymbolicBoolean("SYMBOLIC DEBUG" + id++);
		
		@Override
		public void run() {
			if(cond) {
				System.out.println("Cond is true");
				int ta = 3 + 2;
			}else {
				System.out.println("Cond is false");
				int b = 4 + 2;
				b = 4 + 2;
			}
		}
	}
	
	static class Racer implements Runnable {

		private ConcCompute conc;
		
		public Racer(ConcCompute conc) {
			this.conc = conc;
		}
		
		@Override
		public void run() {
			//this.conc.setcond(true);
			this.conc.cond = true;
		}
		
	}
}
