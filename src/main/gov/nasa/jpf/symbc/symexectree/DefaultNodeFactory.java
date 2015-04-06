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

import gov.nasa.jpf.symbc.symexectree.structure.IfNode;
import gov.nasa.jpf.symbc.symexectree.structure.InvokeNode;
import gov.nasa.jpf.symbc.symexectree.structure.MonitorEnterNode;
import gov.nasa.jpf.symbc.symexectree.structure.MonitorExitNode;
import gov.nasa.jpf.symbc.symexectree.structure.Node;
import gov.nasa.jpf.symbc.symexectree.structure.ReturnNode;
import gov.nasa.jpf.symbc.symexectree.structure.StdNode;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class DefaultNodeFactory extends NodeFactory {

	@Override
	public Node constructStdNode(InstrContext instrCtx) {
		return new StdNode(instrCtx);
	}
	
	@Override
	public IfNode constructIfNode(InstrContext instrCtx) {
		return new IfNode(instrCtx);
	}
	
	@Override
	public InvokeNode constructInvokeNode(InstrContext instrCtx) {
		return new InvokeNode(instrCtx);
	}
	
	@Override
	public ReturnNode constructReturnNode(InstrContext instrCtx) {
		return new ReturnNode(instrCtx);
	}

	@Override
	public MonitorEnterNode constructMonitorEnterNode(InstrContext instrCtx) {
		return new MonitorEnterNode(instrCtx);
	}

	@Override
	public MonitorExitNode constructMonitorExitNode(InstrContext instrCtx) {
		return new MonitorExitNode(instrCtx);
	}
}
