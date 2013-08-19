/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import javax.scj.PeriodicParameters;
import javax.scj.PeriodicThread;
import javax.scj.RealtimeSystem;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SimpleSys extends PeriodicThread {
	
	/**
	 * @param pp
	 */
	public SimpleSys(PeriodicParameters pp) {
		super(pp);
	}
	
	public SimpleSys() {
		super(new PeriodicParameters(200));
	}
	
	public static void main(String[] args) {
		new SimpleSys(new PeriodicParameters(200));
		new SimpleSys(new PeriodicParameters(200));
		new SimpleSys(new PeriodicParameters(200));
		new SimpleSys(new PeriodicParameters(200));
		new SimpleSys(new PeriodicParameters(200));
		
		RealtimeSystem.start();
	}

	public int computation(boolean cond, boolean cond2) {
		int b = 0;
		if(cond) {
			cond2 = !cond;
			if(!cond) { //infeasible
				b = callee(42);
				b = callee(42);
				b = callee(42);
			} else {
				b = callee(42);
				b = 42; //the worst case execution path
			}
			if(!cond2) {//infeasible
				b = callee(42);
				b = callee(42);
				b = callee(42);
			}
		}
		return b;
	}
	
	public int callee(int a) {
		return a + 42;
	}

	@Override
	protected boolean run() {
		computation(false, true);
		return false;
	}
}
