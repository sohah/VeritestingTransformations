/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.symbc.InvokeTest;
import gov.nasa.jpf.symbc.realtime.minepump.scj.PeriodicMethaneDetectionEventHandler;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestPrintMinepump extends InvokeTest {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.realtime.minepump.scj.PeriodicMethaneDetectionEventHandler.run()";
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests;${jpf-symbc}/../SARTSBenchmarks/bin;${jpf-symbc}/../scjNoRelativeTime/bin;${jpf-symbc}/../JOP/bin";
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.symexectree.visualizer.SymExecTreeVisualizerListener";
	private static final String OUTPUTPATH = "+symbolic.visualiser.basepath = ./";
	private static final String FORMAT = "+symbolic.visualiser.outputformat = dot";
	
	
	
	//remember the nosolver option is like a cfg traversal!
	
	//private static final String SOLVER = "+symbolic.dp=no_solver";
	private static final String[] JPF_ARGS = {INSN_FACTORY, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD,
											  OUTPUTPATH,
											  FORMAT
											  };
	@Test
	public void mainTest() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			PeriodicMethaneDetectionEventHandler.main(null);
		}
	}
}
