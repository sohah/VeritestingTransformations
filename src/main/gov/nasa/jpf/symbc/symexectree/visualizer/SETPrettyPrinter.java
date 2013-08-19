/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.jvm.bytecode.InvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.ReturnInstruction;
import gov.nasa.jpf.symbc.symexectree.SymbolicExecutionTree;
import gov.nasa.jpf.symbc.symexectree.Transition;
import gov.nasa.jpf.vm.Instruction;

import java.awt.Color;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

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
		attrs.add(new Attribute(Attribute.NODE, Attribute.LABEL_ATTR, this.getLabelString(treeNode)));
		if(instr instanceof InvokeInstruction) {
			attrs.addAll(this.getInvokeNodeAttr(treeNode));
		} else if(instr instanceof ReturnInstruction) {
			attrs.addAll(this.getReturnNodeAttr(treeNode));
		} else if(instr instanceof IfInstruction) {
			attrs.addAll(this.getIfNodeAttr(treeNode));
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
	 * Override this method if you want a different label string
	 * for the nodes in the graph. Each line MUST end with a '\r'
	 * @param treeNode
	 * @return
	 */
	protected String getLabelString(gov.nasa.jpf.symbc.symexectree.Node treeNode) {
		StringBuilder sb = new StringBuilder();
		sb.append(treeNode.getInstructionContext().getInstr().getMnemonic() + "\r");
		return sb.toString();
	}
	
	/**
	 * Override this method if you want different attributes
	 * for the 'invoke' nodes in the graph.
	 * @param treeNode
	 * @return
	 */
	protected LinkedList<Attribute> getInvokeNodeAttr(gov.nasa.jpf.symbc.symexectree.Node treeNode) {
		LinkedList<Attribute> attrs = new LinkedList<>();
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
