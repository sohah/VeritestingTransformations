package uberlazy;

public class Node {
	
	short elem;
	Node next;
	static int testElem;
	
	public Node () {
		
	}
	public boolean isNextObject (Object node) {
		return this.next == node;
	}
	
	public void print() { 
		System.out.println("I am a just a Node");
	}
}