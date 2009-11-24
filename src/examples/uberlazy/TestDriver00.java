package uberlazy;

/*
 * This class tests building equivalence classes and the partition
 * function for differing shapes when a store operation occurs on
 * a data-structure of a non-primitive type. 
 */


public class TestDriver00 {
	
	static Node m;
	Node n;
	
	public void run(Node m) {
		if(TestDriver00.m != null) {
			Node tmp = TestDriver00.m.next;
			tmp = swapNode(n);
		
		}
	}
	
	private Node swapNode(Node n) {
		if(n != null) {
			if(n.next !=null) {
				Node t = n.next;
				n.next = t.next;
				t.next = n;
				return t;
			}
		}
		return n;
	}
	
	public static void main(String[] args) {
		TestDriver00 tt = new TestDriver00();
		tt.run(m);
	}
	
}