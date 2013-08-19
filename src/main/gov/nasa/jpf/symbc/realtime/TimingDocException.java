/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import java.io.PrintStream;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TimingDocException extends RealTimeRuntimeException{
	public TimingDocException (String details) {
		super(details);
	}

	public TimingDocException (Throwable cause) {
		super(cause);
	}

	public TimingDocException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		out.println("---------------------- Real-time Symbc JPF error stack trace ---------------------");
		super.printStackTrace(out);
	}
}
