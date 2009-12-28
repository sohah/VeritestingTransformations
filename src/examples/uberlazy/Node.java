package uberlazy;

public class Node {
	
	short elem;
	Node next;
	
	public Node () {
		
	}
	public boolean isNextObject (Object node) {
		return this.next == node;
	}
}