/**
 * 
 */
package gov.nasa.jpf.symbc;

import gov.nasa.jpf.vm.ClassInfo;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
@Deprecated
public class InstructionFactoryFilter {
	/*
	 * This class is a quick fix until we fix the filter
	 */
	public InstructionFactoryFilter(Object obj, String[] strs, Object obj2, Object obj3) {
		
	}
	
	public boolean isInstrumentedClass(ClassInfo temp) {
		return true;
	}
	
}
