/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.structure;

import gov.nasa.jpf.jvm.bytecode.LockInstruction;
import gov.nasa.jpf.symbc.symexectree.InstrContext;
import gov.nasa.jpf.vm.Instruction;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public abstract class MonitorNode extends Node {

	protected int lastLocRef;

	public MonitorNode(InstrContext instructionContext) {
		this(instructionContext, null);
	}
	
	public MonitorNode(InstrContext instructionContext, SymbolicExecutionTree tree) {
		super(instructionContext, tree);
		
		/*
		 * TODO: typechecking should be done for all nodes...
		 */
		Instruction instr = instructionContext.getInstr();
		if(!(instr instanceof LockInstruction))
			throw new UnexpectedInstructionTypeException(instr.getClass(), LockInstruction.class);
		
		LockInstruction mInstr = (LockInstruction)instructionContext.getInstr();
		
		this.lastLocRef = mInstr.getLastLockRef();
	}
	
	public int getLastLockRef() {
		return this.lastLocRef;
	}
}
