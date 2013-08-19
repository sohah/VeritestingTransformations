/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import java.io.PrintStream;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class UppaalTranslatorException extends RealTimeRuntimeException {

	public UppaalTranslatorException (String details) {
		super(details);
	}

	public UppaalTranslatorException (Throwable cause) {
		super(cause);
	}

	public UppaalTranslatorException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		out.println("---------------------- Real-time Symbc JPF error stack trace ---------------------");
		super.printStackTrace(out);
	}
}
