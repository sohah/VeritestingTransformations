/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

import gov.nasa.jpf.symbc.symexectree.structure.IfNode;
import gov.nasa.jpf.symbc.symexectree.structure.InvokeNode;
import gov.nasa.jpf.symbc.symexectree.structure.Node;
import gov.nasa.jpf.symbc.symexectree.structure.ReturnNode;
import gov.nasa.jpf.symbc.symexectree.structure.StdNode;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class DefaultNodeFactory extends NodeFactory {

	@Override
	public Node constructStdNode(InstrContext instrCtx) {
		return new StdNode(instrCtx);
	}
	
	@Override
	public IfNode constructIfNode(InstrContext instrCtx) {
		return new IfNode(instrCtx);
	}
	
	@Override
	public InvokeNode constructInvokeNode(InstrContext instrCtx) {
		return new InvokeNode(instrCtx);
	}
	
	@Override
	public ReturnNode constructReturnNode(InstrContext instrCtx) {
		return new ReturnNode(instrCtx);
	}
}
