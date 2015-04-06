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

import java.util.LinkedList;

import gov.nasa.jpf.symbc.symexectree.ISymbolicExecutionTreeElement;
import gov.nasa.jpf.symbc.symexectree.MethodDesc;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTreeVisitor;
import gov.nasa.jpf.symbc.symexectree.Transition;
import gov.nasa.jpf.vm.MethodInfo;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SymbolicExecutionTree implements ISymbolicExecutionTreeElement {
	
	private MethodDesc targetMethod;
	private LinkedList<Node> nodes;
	private LinkedList<Transition> transitions;
	private Node rootNode;
	
	public SymbolicExecutionTree(MethodDesc targetMethod) {
		this.targetMethod = targetMethod;
		this.nodes = new LinkedList();
		this.transitions = new LinkedList();
		this.rootNode = null;
	}
	
	public void addNode(Node node) {
		if(this.rootNode == null)
			this.rootNode = node;
		this.nodes.add(node);
	}

	public void removeNode(Node node) {
		if(node == this.rootNode) {
			this.rootNode = node.getOutgoingTransitions().getFirst().getDstNode();
		}
		this.nodes.remove(node);
	}
	
	public void removeTransition(Transition trans) {
		this.transitions.remove(trans);
	}
	
	public void addTransition(Transition trans) {
		this.transitions.add(trans);
	}
	
	public Node getRootNode() {
		return this.rootNode;
	}
	
	public MethodDesc getTargetMethod() {
		return targetMethod;
	}

	public LinkedList<Node> getNodes() {
		return nodes;
	}

	public LinkedList<Transition> getTransitions() {
		return transitions;
	}

	@Override
	public void accept(SymbolicExecutionTreeVisitor visitor) {
		visitor.visit(this);
		if(this.rootNode != null)
			this.rootNode.accept(visitor);
	}
}
