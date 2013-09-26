/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.symbc.InvokeTest;
import gov.nasa.jpf.symbc.X;

import org.junit.Test;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TestMissedPaths extends InvokeTest {
	private static final String SYM_METHOD = "+symbolic.method=gov.nasa.jpf.symbc.symexectree.visualizer.InstanceFieldPropagation.run()";
		
	private static final String CLASSPATH_UPDATED = "+classpath=${jpf-symbc}/build/tests";
	
	private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.symexectree.visualizer.SymExecTreeVisualizerListener";
	//private static final String LISTENER = "+listener = gov.nasa.jpf.symbc.SymbolicListener";
	private static final String OUTPUTPATH = "+symbolic.visualizer.basepath = ${jpf-symbc}/prettyprint";
	private static final String FORMAT = "+symbolic.visualizer.outputformat = pdf";	
	private static final String DEBUG = "+symbolic.debug = true";
	private static final String LAZY = "+symbolic.lazy = true";

	private static final String[] JPF_ARGS = {INSN_FACTORY, 
											  LISTENER, 
											  CLASSPATH_UPDATED, 
											  SYM_METHOD,
											  OUTPUTPATH,
											  FORMAT,
											  DEBUG,
											  LAZY
											  };

	
	@Test
	public void testInstanceFieldPropagation () {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			InstanceFieldPropagation mp = new InstanceFieldPropagation();
			mp.start();

			X x = new X();
			System.out.println("M: new " + x);
			mp.myX = x;        // (0) x not shared until this GOT executed

			//Thread.yield();  // this would expose the error
			System.out.println("M: x.pass=true");
			x.pass = true;     // (1) need to break BEFORE assignment or no error
		}
	}
}
