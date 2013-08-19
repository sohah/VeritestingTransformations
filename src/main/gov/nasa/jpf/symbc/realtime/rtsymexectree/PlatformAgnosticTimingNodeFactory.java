/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.symbc.symexectree.Node;
import gov.nasa.jpf.symbc.symexectree.NodeFactory;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class PlatformAgnosticTimingNodeFactory extends NodeFactory {

	@Override
	public Node constructNode(InstrContext instrCtx) {
		return new PlatformAgnosticTimingNode(instrCtx);
	}
}
