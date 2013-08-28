/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.rtsymexectree;

import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.symbc.symexectree.Node;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public abstract class RTNode extends Node {

	public RTNode(InstrContext instructionContext) {
		super(instructionContext);
	}
	
	public RTNode(InstrContext instructionContext, SymbolicExecutionTree tree) {
		super(instructionContext, tree);
	}	
}
