/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTreeRuntimeException;

import java.io.PrintStream;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class PrettyPrinterException extends SymbolicExecutionTreeRuntimeException {

	public PrettyPrinterException (String details) {
		super(details);
	}

	public PrettyPrinterException (Throwable cause) {
		super(cause);
	}

	public PrettyPrinterException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		super.printStackTrace(out);
	}
}
