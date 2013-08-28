/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import java.io.PrintStream;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class RealTimeRuntimeException extends RuntimeException{
	public RealTimeRuntimeException (String details) {
		super(details);
	}

	public RealTimeRuntimeException (Throwable cause) {
		super(cause);
	}

	public RealTimeRuntimeException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		out.println("---------------------- Real-time Symbc JPF error stack trace ---------------------");
		super.printStackTrace(out);
	}
}
