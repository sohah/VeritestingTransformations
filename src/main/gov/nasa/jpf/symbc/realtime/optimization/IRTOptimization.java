/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.optimization;

import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public interface IRTOptimization {
	public void conductOptimization(SymbolicExecutionTree tree);
}
