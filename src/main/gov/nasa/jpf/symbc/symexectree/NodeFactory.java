/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public abstract class NodeFactory {

	public NodeFactory() {
		
	}
	
	public abstract Node constructNode(InstrContext instrCtx);
	
	//We do not allow this one to be overrided
	public final Node constructNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		Node n = this.constructNode(instrCtx);
		tree.addNode(n);
		return n;
	}
	
}
