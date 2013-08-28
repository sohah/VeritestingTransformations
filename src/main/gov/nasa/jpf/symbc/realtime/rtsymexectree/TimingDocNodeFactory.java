/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

import gov.nasa.jpf.symbc.realtime.TimingDoc;
import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.symbc.symexectree.Node;
import gov.nasa.jpf.symbc.symexectree.NodeFactory;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class TimingDocNodeFactory extends NodeFactory {

	private TimingDoc tDoc;
	
	public TimingDocNodeFactory(TimingDoc tDoc) {
		this.tDoc = tDoc;
	}
	
	@Override
	public Node constructNode(InstrContext instrCtx) {
		return new TimingDocNode(instrCtx, this.tDoc.get(instrCtx.getInstr()));
	}

}
