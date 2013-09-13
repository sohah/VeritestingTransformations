/**
 * 
 */
package gov.nasa.jpf.symbc.bytecode.util;

import java.util.Set;

import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class ExplicitPCChoiceGenerator extends PCChoiceGenerator {

	private Set<Integer> trueConditions;
	
	public ExplicitPCChoiceGenerator(int size, Set<Integer> trueConditions) {
		super(size);
		this.trueConditions = trueConditions;
	}

	@Override
	public Integer getNextChoice () {
		Integer choice = super.getNextChoice();
		while(!trueConditions.contains(choice)) choice = super.getNextChoice();
		return choice;
	}
	
}
