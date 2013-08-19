/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class PlatformAgnosticTimingNode extends RTNode {

	/**
	 * @param instructionContext
	 */
	public PlatformAgnosticTimingNode(InstrContext instructionContext) {
		super(instructionContext);
	}

	public PlatformAgnosticTimingNode(InstrContext instructionContext, SymbolicExecutionTree tree) {
		super(instructionContext, tree);
	}
}
