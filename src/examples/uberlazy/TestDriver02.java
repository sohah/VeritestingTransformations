package uberlazy;

/**
 * @author Neha Rungta
 *  A test driver for checking the values in the equivalence
 *  classes when variables of primitive type differ in their
 *  values. 
 *  **/

import gov.nasa.jpf.symbc.Symbolic;


public class TestDriver02 {
	
	@Symbolic("true")
	Node n;
	@Symbolic("true")
	Node m;
	
	public void run() {
		if(m != null) {
			if(m.elem > 10) {
				System.out.println("the value of m.elem is greater 10");
				differentField();
			}
		}
	}
	
	public void differentField() {
		if(n != null) {
			// when a primitive field reference is read	
			// and it differs in the value then the partition
			// function separates the ones that are different 
			if(n.elem < 5) { 
				System.out.println("the value of n.elem is less 5");
			} 
		}
	}
	
	public static void main(String[] args) {
		TestDriver02 tt = new TestDriver02();
		tt.run();
	}
	
}