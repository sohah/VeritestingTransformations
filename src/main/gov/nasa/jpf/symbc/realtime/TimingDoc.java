/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import java.util.HashMap;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TimingDoc extends HashMap<String, InstructionTimingInfo>{

	private static final long serialVersionUID = 1L;

	@Override
	public InstructionTimingInfo get(Object key) {
		InstructionTimingInfo tInfo = super.get(key);
		if(tInfo != null)
			return tInfo;
		else {
			if(key instanceof String) {
				return new InstructionTimingInfo((String)key, -1, 100, 100);
			} else {
				throw new RealTimeRuntimeException("[" + key.toString() + "] is not a String!");
			}
		}
	}
}
