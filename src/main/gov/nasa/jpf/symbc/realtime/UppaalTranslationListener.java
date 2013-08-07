/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class UppaalTranslationListener extends PropertyListenerAdapter {
	
	
	public UppaalTranslationListener() {
		
	}
	
	@Override
	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {
		
	}
	

}
