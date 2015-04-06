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

import gov.nasa.jpf.vm.Instruction;

import java.io.PrintStream;


/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class UnexpectedInstructionTypeException extends RuntimeException {
	
	public UnexpectedInstructionTypeException (Class<? extends Instruction> class1, Class<? extends Instruction> class2) {
		this("Got instruction with type [" + class1.getCanonicalName() + "] but expected instruction type: [" + class2.getCanonicalName() + "]");
	}
	
	public UnexpectedInstructionTypeException (String details) {
		super(details);
	}

	public UnexpectedInstructionTypeException (Throwable cause) {
		super(cause);
	}

	public UnexpectedInstructionTypeException (String details, Throwable cause){
		super(details, cause);
	}
	
	public void printStackTrace (PrintStream out) {
		out.println("---------------------- Symbolic Execution Tree JPF error stack trace ---------------------");
		super.printStackTrace(out);
	}
}
