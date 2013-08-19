/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class DefaultNodeFactory extends NodeFactory {

	@Override
	public Node constructNode(InstrContext instrCtx) {
		return new Node(instrCtx);
	}
}
