/**
 * 
 */
package gov.nasa.jpf.symbc.realtime.optimization;

import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class RTOptimizer {

	private List<IRTOptimization> optimizations;
	
	public RTOptimizer(List<IRTOptimization> optimizations) {
		this.optimizations = optimizations;
	}
	
	public RTOptimizer() {
		this(new LinkedList<IRTOptimization>());
	}
	
	public void addOptimization(IRTOptimization optimization) {
		this.optimizations.add(optimization);
	}
	
	public void optimize(SymbolicExecutionTree tree) {
		for(IRTOptimization opt : this.optimizations) {
			opt.conductOptimization(tree);
		}
	}
}
