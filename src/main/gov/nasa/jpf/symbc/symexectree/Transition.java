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

import gov.nasa.jpf.symbc.symexectree.structure.Node;
import gov.nasa.jpf.symbc.symexectree.structure.SymbolicExecutionTree;

import org.apache.commons.lang.builder.EqualsBuilder;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class Transition implements ISymbolicExecutionTreeElement {

	private Node srcNode;
	private Node dstNode;
	
	public Transition(Node src, Node dst) {
		this.srcNode = src;
		this.srcNode.addOugoingTransitions(this);
		this.dstNode = dst;
		this.dstNode.addIncomingTransition(this);
	}
	
	public Transition(Node src, Node dst, SymbolicExecutionTree tree) {
		this(src, dst);
		tree.addTransition(this);
	}
	
	public Node getSrcNode() {
		return srcNode;
	}
	
	public Node getDstNode() {
		return dstNode;
	}
	
	public void setSrcNode(Node srcNode) {
		this.srcNode = srcNode;
	}

	public void setDstNode(Node dstNode) {
		this.dstNode = dstNode;
	}

	@Override
	public void accept(SymbolicExecutionTreeVisitor visitor) {
		visitor.visit(this);
		this.dstNode.accept(visitor);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((dstNode == null) ? 0 : dstNode.hashCode());
		result = prime * result + ((srcNode == null) ? 0 : srcNode.hashCode());
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
		Transition other = (Transition) obj;
		
		return new EqualsBuilder().append(srcNode, other.srcNode)
								  .append(dstNode, other.dstNode)
								  .isEquals();
	}
	
}
