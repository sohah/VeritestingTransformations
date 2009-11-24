package uberlazy;

/*
 * 
 */

public class TestDriver01 {
	
	Node n;

	
	public void run () {
		if(n != null) {
			if(n instanceof dblNode) {
				System.out.println("You can store reals in this data structure");
			} else {
				System.out.println("Don't store a real number in here");
			}
		}
	}
	
	public static void main(String[] args) {
		TestDriver01 tt = new TestDriver01();
		tt.run();
	}
	
}