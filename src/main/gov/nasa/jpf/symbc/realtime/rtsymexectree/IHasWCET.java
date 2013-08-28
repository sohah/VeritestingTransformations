/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public interface IHasWCET  {
	public int getWCET();
	public void setWCET(int wcet);
}
