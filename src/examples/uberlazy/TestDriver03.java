package uberlazy;

/**
 * @author Neha Rungta
 * Check for the partitioning of equivalence classes
 * when the instanceof operator is invoked 
 */

import gov.nasa.jpf.symbc.Symbolic;


public class TestDriver03{

	@Symbolic("true")
	Node n;

	public void run() {
		if(n != null ) {
			if(n instanceof intNode) {
				System.out.println("it is an instance of intNode");
			} else if (n instanceof Node) {
				System.out.println("it is an instance of Node class");
			}
		}
	}
	
	public static void main (String[] args) {
		TestDriver03 tt = new TestDriver03();
		tt.run();
	}
	
}