/**
 * 
 */
package gov.nasa.jpf.symbc.realtime;

import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.symbc.realtime.rtsymexectree.IHasBCET;
import gov.nasa.jpf.symbc.realtime.rtsymexectree.IHasWCET;
import gov.nasa.jpf.symbc.symexectree.Node;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;
import gov.nasa.jpf.symbc.symexectree.Transition;
import gov.nasa.jpf.symbc.symexectree.visualizer.PrettyPrinterException;
import gov.nasa.jpf.vm.Instruction;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import uppaal.Automaton;
import uppaal.Location;
import uppaal.NTA;
import uppaal.Location.LocationType;
import uppaal.labels.Synchronization;
import uppaal.labels.Synchronization.SyncType;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class UppaalTranslator {
	private HashMap<Node, Location> visitedTreeNodesMap;
	private boolean targetTetaSARTS;
	private int uniqueID;
	
	private Location finalLoc;
	
	public UppaalTranslator(boolean targetTetaSARTS) {
		this.targetTetaSARTS = targetTetaSARTS;
		this.uniqueID = 0;
	}
	
	public NTA translateSymTree(SymbolicExecutionTree tree) {
		this.visitedTreeNodesMap = new HashMap<Node, Location>(); 
		
		Automaton ta = new Automaton(tree.getTargetMethod().getShortMethodName());
		Location initLoc = new Location(ta, "initLoc");
		ta.setInit(initLoc);
		this.finalLoc = new Location(ta, "final");
		this.finalLoc.setType(LocationType.COMMITTED);
		ta.getDeclaration().add("clock executionTime;");

		Location taRoot = recursivelyTraverseSymTree(tree.getRootNode(), ta);
		uppaal.Transition initTrans = new uppaal.Transition(ta, initLoc, taRoot);
		if(this.targetTetaSARTS) {
			ta.setParameter("const ThreadID tID");
			uppaal.Transition finalTrans = new uppaal.Transition(ta, finalLoc, initLoc);
			finalTrans.setSync(new Synchronization("run[tID]", SyncType.INITIATOR));
			initTrans.setSync(new Synchronization("run[tID]", SyncType.RECEIVER));
		} else {
			initLoc.setType(LocationType.COMMITTED);
		}
		
		NTA nta = new NTA();
		if(!this.targetTetaSARTS) {
			nta.getSystemDeclaration().addSystemInstance(ta.getName().getName());
			nta.getDeclarations().add("clock globalClock;");
		}
		nta.addAutomaton(ta);
		return nta;
	}
	
	private String getUniqueIDString() {
		return Integer.toString(this.uniqueID++);
	}
	
	private Location recursivelyTraverseSymTree(Node treeNode, Automaton ta) {
		if(visitedTreeNodesMap.containsKey(treeNode)) {
			return visitedTreeNodesMap.get(treeNode);
		}
		List<Transition> outTransitions = treeNode.getOutgoingTransitions();
		Location targetLoc = null;
		if(skipNode(treeNode)) {
			for(Transition outTrans : outTransitions) {
				return recursivelyTraverseSymTree(outTrans.getDstNode(), ta);
			}
		}
		
		targetLoc = translateTreeNode(treeNode, ta);
		visitedTreeNodesMap.put(treeNode, targetLoc);
		
		//A leaf has been hit, so we add a transition to the final location
		if(outTransitions.isEmpty()) { 
			uppaal.Transition uppFinalTrans = new uppaal.Transition(ta, targetLoc, this.finalLoc);
			patchTransition(uppFinalTrans, treeNode);
		} else {
			for(Transition t : outTransitions) {
				uppaal.Transition uppTrans = new uppaal.Transition(ta, targetLoc, recursivelyTraverseSymTree(t.getDstNode(), ta));
				this.patchTransition(uppTrans, treeNode);

			}
		}
		return targetLoc;
	}
	
	/*We skip certain nodes when translating to UPPAAL
	 * Internally, JPF has certain instructions e.g. executenative,
	 * directcallreturn, nativereturn etc. which are not part of
	 * the JVM spec and as such, do not have an execution time
	 * defined by most platforms.
	 */
	private boolean skipNode(Node node) {
		Instruction instr = node.getInstructionContext().getInstr();
		if(instr.getByteCode() > 255)
			return true;
		if(instr.getMethodInfo().getClassInfo().getPackageName().contains("gov.nasa.jpf.symbc") &&
		   instr.getMethodInfo().getClassName().equals("Debug"))
			return true;
		return false;
	}
	
	private void patchTransition(uppaal.Transition uppTrans, Node treeNode) {
		if(!(treeNode instanceof IHasBCET) &&
		   !(treeNode instanceof IHasWCET)) {
			if(this.targetTetaSARTS)
				uppTrans.setGuard("running[tID] = true");
			uppTrans.setSync(new Synchronization("jvm_execute", SyncType.INITIATOR));
			uppTrans.addUpdate("jvm_instruction = JVM_" + treeNode.getInstructionContext().getInstr().getMnemonic());
		} else if((treeNode instanceof IHasBCET) &&
				  (treeNode instanceof IHasWCET)) {
			uppTrans.setGuard("executionTime >= " + ((IHasBCET) treeNode).getBCET() + "&&\n" +
							  "executionTime <= " + ((IHasWCET) treeNode).getWCET());
			uppTrans.addUpdate("executionTime = 0");
		}
		else if(treeNode instanceof IHasWCET) {
			uppTrans.setGuard("executionTime == " + ((IHasWCET) treeNode).getWCET());
			uppTrans.addUpdate("executionTime = 0");
		}
	}
	
	private Location translateTreeNode(Node treeNode, Automaton ta) {
		Instruction instr = treeNode.getInstructionContext().getInstr();
		Location newLoc = new Location(ta, instr.getMnemonic() + "_" + this.getUniqueIDString());
		StringBuilder invariantBuilder = new StringBuilder();
		if(treeNode instanceof IHasWCET) {
			invariantBuilder.append("executionTime <= ")
							.append(((IHasWCET) treeNode).getWCET());
		}
		if(treeNode instanceof IHasBCET) {
			invariantBuilder.append("&&\n")
							.append("executionTime >= ")
							.append(((IHasBCET) treeNode).getBCET());
		}
		if(targetTetaSARTS) {
			invariantBuilder.append("&&\n")
							.append("executionTime' == running[tID]");
		}
		newLoc.setInvariant(invariantBuilder.toString());
		
		return newLoc;
	}
}
