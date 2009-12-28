package uberlazy;

import gov.nasa.jpf.symbc.Symbolic;

public class TestDriver04{ 
	
	@Symbolic("true")
	Node n; 
	
	public void run() {
		
		intNode m = new intNode();
		
		if(n != null) {
			n.isNextObject(m);
		}
	}
	
	public static void main(String[] args) {
		TestDriver04 tt = new TestDriver04();
		tt.run();
	}
}