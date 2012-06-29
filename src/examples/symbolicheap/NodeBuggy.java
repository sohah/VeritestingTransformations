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
    
	void addSimple2() {
    	int depth = 2;
    	NodeBuggy bigson = this;
    	while ((bigson.left != null || bigson.right != null) && depth > 0) {
    		depth--;
    		System.out.println("depth = " + depth);
    		if (bigson.right != null) {
    			bigson = bigson.right;			
    		} else {
    			bigson = bigson.left;
    		}
		}
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
    	System.out.println("doing ExLazy.Node RunTest!!!!");
    	NodeBuggy X = new NodeBuggy(5);
        X = (NodeBuggy) Debug.makeSymbolicRef("input_X", X);
        if (X != null) {
            X.addSimple3();
        }
        Debug.printSymbolicRef(X, "node = ");
    }
	
	public static void main(String[] args) {	
		System.out.println("Please just do something");
		runTest(1);
	}

}
