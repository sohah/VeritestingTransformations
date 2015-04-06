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
import gov.nasa.jpf.symbc.symexectree.structure.SymbolicExecutionTree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public abstract class NodeFactory {

	public NodeFactory() {
		
	}
	public abstract MonitorEnterNode constructMonitorEnterNode(InstrContext instrCtx);
	
	public abstract MonitorExitNode constructMonitorExitNode(InstrContext instrCtx);
	
	public abstract Node constructStdNode(InstrContext instrCtx);
	
	public abstract IfNode constructIfNode(InstrContext instrCtx);

	public abstract InvokeNode constructInvokeNode(InstrContext instrCtx);

	public abstract ReturnNode constructReturnNode(InstrContext instrCtx);
	
	public final MonitorEnterNode constructMonitorEnterNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		MonitorEnterNode n = this.constructMonitorEnterNode(instrCtx);
		tree.addNode(n);
		return n;
	}
	
	public final MonitorExitNode constructMonitorExitNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		MonitorExitNode n = this.constructMonitorExitNode(instrCtx);
		tree.addNode(n);
		return n;
	}	
	
	public final Node constructStdNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		Node n = this.constructStdNode(instrCtx);
		tree.addNode(n);
		return n;
	}
	
	public final IfNode constructIfNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		IfNode n = this.constructIfNode(instrCtx);
		tree.addNode(n);
		return n;
	}
	
	public final InvokeNode constructInvokeNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		InvokeNode n = this.constructInvokeNode(instrCtx);
		tree.addNode(n);
		return n;
	}
	
	public final ReturnNode constructReturnNode(InstrContext instrCtx, SymbolicExecutionTree tree) {
		ReturnNode n = this.constructReturnNode(instrCtx);
		tree.addNode(n);
		return n;
	}
	
}
