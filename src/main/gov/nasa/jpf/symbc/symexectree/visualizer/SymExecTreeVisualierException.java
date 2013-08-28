/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import java.io.PrintStream;

import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTreeRuntimeException;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SymExecTreeVisualierException extends SymbolicExecutionTreeRuntimeException {

	public SymExecTreeVisualierException (String details) {
		super(details);
	}

	public SymExecTreeVisualierException (Throwable cause) {
		super(cause);
	}

	public SymExecTreeVisualierException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		super.printStackTrace(out);
	}
}
