/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import java.io.PrintStream;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class UnknownReturnTypeException extends RealTimeRuntimeException {

	public UnknownReturnTypeException (String details) {
		super(details);
	}

	public UnknownReturnTypeException (Throwable cause) {
		super(cause);
	}

	public UnknownReturnTypeException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		out.println("---------------------- Real-time Symbc JPF error stack trace ---------------------");
		super.printStackTrace(out);
	}
}
