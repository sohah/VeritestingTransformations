/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import java.io.PrintStream;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class InstructionNotImplementedException extends RealTimeRuntimeException {

	public InstructionNotImplementedException (String details) {
		super(details);
	}

	public InstructionNotImplementedException (Throwable cause) {
		super(cause);
	}

	public InstructionNotImplementedException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		out.println("---------------------- Real-time Symbc JPF error stack trace ---------------------");
		super.printStackTrace(out);
	}
}
