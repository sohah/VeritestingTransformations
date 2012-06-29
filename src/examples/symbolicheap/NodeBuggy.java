package symbolicheap;

import gov.nasa.jpf.symbc.Debug;

public class NodeBuggy {

	int elem;
    NodeBuggy next;
    NodeBuggy left;
    NodeBuggy right;
	
    public NodeBuggy(int x) {
    	elem = x;
    	next = null;
    	left = null;
    	right = null;
    }
	
	void addSimple3() {
		int depth = 0;
    	NodeBuggy bigson = this;
    	while (bigson.left != null || bigson.right != null) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
    		depth++;
    		if (depth == 2)
    			return;
		}
	}
	
	void addSimple4() {
    	NodeBuggy bigson = this;
    	if (bigson.left != null || bigson.right != null) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
		}
    	if (bigson.left != null || bigson.right != null) {
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
		}
	}
	
	public static void runTest(int x) {
    	NodeBuggy X = new NodeBuggy(5);
        X = (NodeBuggy) Debug.makeSymbolicRef("input_X", X);
        if (X != null) {
            X.addSimple3();//broken
            //X.addSimple4(); //working
        }
        Debug.printSymbolicRef(X, "node = ");
    }
	
	public static void main(String[] args) {	
		runTest(1);
	}

}
