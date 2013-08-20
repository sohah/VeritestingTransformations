/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

import java.util.LinkedList;

import uppaal.NTA;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.util.ObjectList.Iterator;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public abstract class ASymbolicExecutionTreeListener extends PropertyListenerAdapter {

	private SymbolicExecutionTreeGenerator SETGenerator;
	protected Config jpfConf;
	
	public ASymbolicExecutionTreeListener(Config conf, JPF jpf) {
		this.jpfConf = conf;
		this.SETGenerator = new SymbolicExecutionTreeGenerator(conf, this.getNodeFactory());
	}
	
	protected abstract NodeFactory getNodeFactory();
	protected abstract void doneConstructingSymbExecTree(LinkedList<SymbolicExecutionTree> trees);

	@Override
	public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
		if (!vm.getSystemState().isIgnored()) {
			MethodInfo mi = instructionToExecute.getMethodInfo();
			
			if(SymExecTreeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
				if(!(instructionToExecute instanceof IfInstruction) ||
				    (instructionToExecute instanceof IfInstruction) &&
					 !currentThread.isFirstStepInsn()) {
					this.SETGenerator.build(new InstrContext(instructionToExecute, 
															 currentThread.getTopFrame(),
															 PathCondition.getPC(vm)));
				}
			}
		}
	}
	
	@Override
	public void searchFinished(Search search) {
		LinkedList<SymbolicExecutionTree> trees = this.SETGenerator.getTrees();
		doneConstructingSymbExecTree(trees);
	}
		
	@Override
	public void choiceGeneratorRegistered(VM vm, ChoiceGenerator<?> nextCG, ThreadInfo currentThread, Instruction executedInstruction) {
		MethodInfo mi = executedInstruction.getMethodInfo();
		if(SymExecTreeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
			this.SETGenerator.addChoice(new InstrContext(executedInstruction, 
														 currentThread.getTopFrame(),
														 PathCondition.getPC(vm)));
		}
	}
	
	@Override
	public void stateBacktracked(Search search) {
		if(SymExecTreeUtils.isInSymbolicCallChain(search.getVM().getInstruction().getMethodInfo(), search.getVM().getCurrentThread().getTopFrame(), this.jpfConf)) {
			this.SETGenerator.restoreChoice(new InstrContext(search.getVM().getInstruction(), 
											search.getVM().getCurrentThread().getTopFrame(),
											PathCondition.getPC(search.getVM())));
		}
	}	
}
