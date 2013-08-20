/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;
import gov.nasa.jpf.symbc.symexectree.Transition;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;

import java.awt.Color;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.apache.commons.lang.SystemUtils;

import att.grappa.Attribute;
import att.grappa.Edge;
import att.grappa.Graph;
import att.grappa.Node;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SETPrettyPrinter {
	
	private HashMap<gov.nasa.jpf.symbc.symexectree.Node, Node> visitedTreeNodesMap;
	private PRETTYPRINTER_FORMAT format;

	private int uniqueID;
	
	public SETPrettyPrinter(PRETTYPRINTER_FORMAT format) {
		this.format = format;
		this.uniqueID = 0;
	}
	
	public void prettyPrintSymTrees(List<SymbolicExecutionTree> trees, String dotOutputBasePath) throws PrettyPrinterException {
		for(SymbolicExecutionTree g : trees) {
			try {
				prettyPrintSymTree(g, dotOutputBasePath);
			} catch (Exception e) {
				throw new PrettyPrinterException(e);
			}
		}
	}
	
	public void prettyPrintSymTree(SymbolicExecutionTree tree, String dotOutputBasePath) throws FileNotFoundException, InterruptedException {
		Graph grappaGraph = makeGrappaGraph(tree);
		File file = new File(dotOutputBasePath + 
							 ((dotOutputBasePath.endsWith("/")) ? "" : "/") + 
							 tree.getTargetMethod().getShortMethodName() + ".dot"); 
		FileOutputStream fo = new FileOutputStream(file);
		grappaGraph.printGraph(fo);
		
		try {
			fo.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		if(format != PRETTYPRINTER_FORMAT.DOT) {
			if(!(SystemUtils.IS_OS_LINUX ||
				 SystemUtils.IS_OS_MAC_OSX ||
				 SystemUtils.IS_OS_MAC))
				throw new PrettyPrinterException("UNIX-like OS required for outputting symbolic execution tree as " + format.getFormat());
			convertDotFile(file, format);
			file.delete();
		}
	}
	
	private Graph makeGrappaGraph(SymbolicExecutionTree tree) {
		visitedTreeNodesMap = new HashMap<gov.nasa.jpf.symbc.symexectree.Node, Node>();
		Graph grappaGraph = new Graph(tree.getTargetMethod().getShortMethodName());
		Attribute graphAttr = new Attribute(Attribute.SUBGRAPH, 
										   	Attribute.LABEL_ATTR, 
										   	tree.getTargetMethod().getShortMethodName());
		grappaGraph.setAttribute(graphAttr);
		
		recursivelyTraverseSymTree(tree.getRootNode(), grappaGraph);
		return grappaGraph;
	}
	
	private Node recursivelyTraverseSymTree(gov.nasa.jpf.symbc.symexectree.Node treeNode, Graph grappaGraph) {
		if(visitedTreeNodesMap.containsKey(treeNode)) {
			return visitedTreeNodesMap.get(treeNode);
		}
		Instruction instr = treeNode.getInstructionContext().getInstr();
		Node targetNode = new Node(grappaGraph, instr.getMnemonic() + this.uniqueID++);
		
		LinkedList<Attribute> attrs = new LinkedList<>();
		if(instr instanceof InvokeInstruction) {
			attrs.addAll(this.getInvokeNodeAttr(treeNode));
		} else if(instr instanceof ReturnInstruction) {
			attrs.addAll(this.getReturnNodeAttr(treeNode));
		} else if(instr instanceof IfInstruction) {
			attrs.addAll(this.getIfNodeAttr(treeNode));
		} else {
			attrs.addAll(this.getNormalNodeAttr(treeNode));
		}
		for(Attribute attr : attrs)
			targetNode.setAttribute(attr);
			
		visitedTreeNodesMap.put(treeNode, targetNode);
		for(Transition t : treeNode.getOutgoingTransitions()) {
			Edge basicBlockEdge = new Edge(grappaGraph, 
										   targetNode, 
										   recursivelyTraverseSymTree(t.getDstNode(), grappaGraph));
			grappaGraph.addEdge(basicBlockEdge);
		}
		return targetNode;
	}
	
	/**
	 * Override this method if you want different attributes
	 * for the 'normal' nodes (e.g. aload, istore) in the graph.
	 * @param treeNode
	 * @return
	 */
	protected LinkedList<Attribute> getNormalNodeAttr(gov.nasa.jpf.symbc.symexectree.Node treeNode) {
		LinkedList<Attribute> attrs = new LinkedList<>();
		
		StringBuilder lblBuilder = new StringBuilder();
		lblBuilder.append(treeNode.getInstructionContext().getInstr().getMnemonic()).append("\\n");
		
		for(Transition in : treeNode.getIncomingTransitions()) {
			gov.nasa.jpf.symbc.symexectree.Node srcNode = in.getSrcNode();
			if(srcNode.getInstructionContext().getInstr() instanceof IfInstruction) {
				PathCondition pc = treeNode.getInstructionContext().getPathCondition();
				if(pc != null) {
					lblBuilder.append("Path condition:\\n");
					String[] pcs = pc.header.stringPC().split("&&");	
					for(int i = 0; i < pcs.length; i++) {
						lblBuilder.append(pcs[i]);
						if(i != pcs.length - 1)
							lblBuilder.append(" &&\\n");
					}
					lblBuilder.append("\r");
				}
			}
		}
		attrs.add(new Attribute(Attribute.NODE, Attribute.LABEL_ATTR, lblBuilder.toString()));
		
		return attrs;
	}
	
	/**
	 * Override this method if you want different attributes
	 * for the 'invoke' nodes in the graph.
	 * @param treeNode
	 * @return
	 */
	protected LinkedList<Attribute> getInvokeNodeAttr(gov.nasa.jpf.symbc.symexectree.Node treeNode) {
		LinkedList<Attribute> attrs = new LinkedList<>();
		
		StringBuilder lblBuilder = new StringBuilder();
		lblBuilder.append(treeNode.getInstructionContext().getInstr().getMnemonic()).append("\\n");
		
		Instruction instr = treeNode.getInstructionContext().getInstr();
		if(instr instanceof InvokeInstruction) { // Should not be necessary, but better safe than sorry
			InvokeInstruction invokeInstr = (InvokeInstruction) instr;
			lblBuilder.append("Calling: ")
					  .append(invokeInstr.getInvokedMethod().getBaseName());
		}
		attrs.add(new Attribute(Attribute.NODE, Attribute.LABEL_ATTR, lblBuilder.toString()));
		attrs.add(new Attribute(Attribute.NODE, Attribute.COLOR_ATTR, Color.red));
		attrs.add(new Attribute(Attribute.NODE, Attribute.SHAPE_ATTR, Attribute.BOX_SHAPE));
		return attrs;
	}
	
	/**
	 *  Override this method if you want different attributes
	 * for the 'return' nodes in the graph.
	 * @param treeNode
	 * @return
	 */
	protected LinkedList<Attribute> getReturnNodeAttr(gov.nasa.jpf.symbc.symexectree.Node treeNode) {
		LinkedList<Attribute> attrs = new LinkedList<>();
		
		StringBuilder lblBuilder = new StringBuilder();
		lblBuilder.append(treeNode.getInstructionContext().getInstr().getMnemonic()).append("\\n");
		
		Instruction instr = treeNode.getInstructionContext().getInstr();
		if(instr instanceof ReturnInstruction) { // Should not be necessary, but better safe than sorry
			StackFrame frame = treeNode.getInstructionContext().getFrame().getPrevious();
			if(frame != null)
				lblBuilder.append("Returning to: ").append(frame.getMethodInfo().getBaseName());
		}
		attrs.add(new Attribute(Attribute.NODE, Attribute.LABEL_ATTR, lblBuilder.toString()));
		attrs.add(new Attribute(Attribute.NODE, Attribute.COLOR_ATTR, Color.red));
		attrs.add(new Attribute(Attribute.NODE, Attribute.SHAPE_ATTR, Attribute.BOX_SHAPE));
		return attrs;
	}
	
	/**
	 *  Override this method if you want different attributes
	 * for the 'if' nodes in the graph.
	 * @param treeNode
	 * @return
	 */
	protected LinkedList<Attribute> getIfNodeAttr(gov.nasa.jpf.symbc.symexectree.Node treeNode) {
		LinkedList<Attribute> attrs = new LinkedList<>();
		Instruction instr = treeNode.getInstructionContext().getInstr();
		StringBuilder lblBuilder = new StringBuilder();
		lblBuilder.append(instr.getMnemonic()).append("\\n");
		lblBuilder.append("(").append(instr.getFilePos()).append(")");
		
		attrs.add(new Attribute(Attribute.NODE, Attribute.LABEL_ATTR, lblBuilder.toString()));
		attrs.add(new Attribute(Attribute.NODE, Attribute.COLOR_ATTR, Color.blue));
		attrs.add(new Attribute(Attribute.NODE, Attribute.SHAPE_ATTR, Attribute.DIAMOND_SHAPE));
		return attrs;
	}
	
	/**
	 * @param file
	 * @throws InterruptedException
	 */
	private void convertDotFile(File file, PRETTYPRINTER_FORMAT format) throws InterruptedException {
		String dotCmd = "dot " + file.getAbsolutePath() + " -T" + format.getFormat() + "-o " + file.getAbsolutePath().replace(".dot", ".png");
		try {
			Process p = Runtime.getRuntime().exec(dotCmd);
			p.waitFor();
			p.exitValue();
			p.destroy();
			
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
