package gov.nasa.jpf.symbc.string.graph;

import gov.nasa.jpf.symbc.numeric.SymbolicInteger;

import java.util.List;

public interface Edge {
	public String getName ();
	
	public Vertex getSource();
	
	public void setSource(Vertex v);
	
	public List<Vertex> getSources ();
	
	public Vertex getDest ();
	
	public void setDest (Vertex v);
	
	public boolean isHyper ();
	
	public boolean isDirected ();
	
	public boolean allVertecisAreConstant();
}
