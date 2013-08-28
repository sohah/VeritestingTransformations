/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree;

import java.util.LinkedList;

import uppaal.NTA;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.FieldInstruction;
import gov.nasa.jpf.jvm.bytecode.GETFIELD;
import gov.nasa.jpf.jvm.bytecode.GETSTATIC;
import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.util.ObjectList.Iterator;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassLoaderInfo;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.FieldInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;

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
	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {
		if (!vm.getSystemState().isIgnored()) {
			MethodInfo mi = executedInstruction.getMethodInfo();
			if(SymExecTreeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
				if(executedInstruction instanceof GETFIELD ||
				   executedInstruction instanceof GETSTATIC) {
					ThreadInfo ti = vm.getCurrentThread();
					if(ti.getTopFrame() != null) {
						if(ti.getTopFrame().getSlots().length > 0) {
							FieldInstruction fieldInstr = (FieldInstruction) executedInstruction;
							ElementInfo ei = fieldInstr.peekElementInfo(ti);
							if(ei != null) {
								if(ei.isShared()) {
									if(!ei.hasFieldAttr(Expression.class) && !ei.isFrozen()) {//Assuming the if the field already has an attr of type Expression, it is symbolic.
										FieldInfo fi = fieldInstr.getFieldInfo();
										ei.addFieldAttr(fi, new SymbolicInteger("SHARED SYMB " + symbID++));								
									}
								}
							}
						}
					}
				}
			}
		}
	}
	
	@Override
	public void executeInstruction(VM vm, ThreadInfo currentThread, Instruction instructionToExecute) {
		if (!vm.getSystemState().isIgnored()) {
			MethodInfo mi = instructionToExecute.getMethodInfo();
			if(SymExecTreeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
				this.SETGenerator.generate(new InstrContext(instructionToExecute, 
															 currentThread.getTopFrame(),
															 PathCondition.getPC(vm)));
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
		if (!vm.getSystemState().isIgnored()) { //Not sure if this check is necessary...
			if(nextCG instanceof PCChoiceGenerator) {
				MethodInfo mi = executedInstruction.getMethodInfo();
				if(SymExecTreeUtils.isInSymbolicCallChain(mi, currentThread.getTopFrame(), this.jpfConf)) {
					this.SETGenerator.addChoice(new InstrContext(executedInstruction, 
																 currentThread.getTopFrame(),
																 PathCondition.getPC(vm)));
				}
			}
		}
	}
	
	@Override
	public void stateBacktracked(Search search) {
		if (!search.getVM().getSystemState().isIgnored()) {
			if(search.getVM().getChoiceGenerator() instanceof PCChoiceGenerator) {
				if(SymExecTreeUtils.isInSymbolicCallChain(search.getVM().getInstruction().getMethodInfo(), search.getVM().getCurrentThread().getTopFrame(), this.jpfConf)) {
					this.SETGenerator.restoreChoice(new InstrContext(search.getVM().getInstruction(), 
													search.getVM().getCurrentThread().getTopFrame(),
													PathCondition.getPC(search.getVM())));
				}
			}
		}
	}
	
	private int symbID = 0;
	private boolean hasStarted = false;
	@Override
	public void choiceGeneratorAdvanced (VM vm, ChoiceGenerator<?> currentCG) {
		if (!vm.getSystemState().isIgnored()) { //Not sure if this check is necessary...
			if(currentCG instanceof ThreadChoiceFromSet) {
				ThreadChoiceFromSet tc = (ThreadChoiceFromSet) currentCG;				
				ThreadInfo tiChoices[] = tc.getChoices();				
				for(int i = 0; i < tiChoices.length; i++) {
					if(tiChoices[i].getTopFrame() != null) { //We select the thread executing the symbolic method(s) we are targeting
						MethodInfo mInfos[] = tiChoices[i].getTopFrame().getClassInfo().getDeclaredMethodInfos();
						for(MethodInfo mInfo : mInfos) {
							if(SymExecTreeUtils.isMethodInfoSymbolicTarget(mInfo, this.jpfConf)) {
								tc.select(i);
								hasStarted = true;
								return;
							}
						}
					}
				}
				if(hasStarted)
					vm.ignoreState(true);
			}
		}
	}
}
