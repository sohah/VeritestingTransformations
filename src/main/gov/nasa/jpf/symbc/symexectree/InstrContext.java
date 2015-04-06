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
package gov.nasa.jpf.symbc.symexectree;

import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class InstrContext {
	
	private final Instruction instr;
	private final StackFrame frame;
	private final PathCondition pc;
	private final ThreadInfo threadInfo;
	private final int execInstrNum;
	
	public InstrContext(Instruction instr, StackFrame frame, ThreadInfo threadInfo) {
		this(instr, frame, threadInfo, null);
	}
	
	public InstrContext(Instruction instr, StackFrame frame, ThreadInfo threadInfo, PathCondition pc) {
		this.instr = instr;
		this.frame = frame;
		this.pc = pc;
		this.threadInfo = threadInfo;
		execInstrNum = threadInfo.getExecutedInstructions();
	}
	
	public Instruction getInstr() {
		return instr;
	}
	
	public StackFrame getFrame() {
		return frame;
	}
	
	public PathCondition getPathCondition() {
		return this.pc;
	}
	
	public ThreadInfo getThreadInfo() {
		return this.threadInfo;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((frame == null) ? 0 : frame.hashCode());
		result = prime * result + ((instr == null) ? 0 : instr.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		InstrContext other = (InstrContext) obj;

		if (frame == null) {
			if (other.frame != null)
				return false;
		} else if (!frame.equals(other.frame)) {
			return false;
		}
		
		if (pc == null) {
			if (other.pc != null)
				return false;
		} else if(pc != null) {
			if (other.pc == null)
				return false;
			if(!this.pc.equals(other.pc))
				return false;
		}
		
		if (instr == null) {
			if (other.instr != null)
				return false;
		} else if(!instr.getMnemonic().equals(other.instr.getMnemonic())) {
			return false;
		} else if(instr.getInstructionIndex() != other.instr.getInstructionIndex()) {
			return false;
		}
		return true;
	}
}
