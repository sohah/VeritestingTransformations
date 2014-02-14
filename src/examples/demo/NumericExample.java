package demo;

import gov.nasa.jpf.symbc.Debug;

public class NumericExample {

	public static void test(int a, int b) {
	    int c = a/(b+a -2);                
	    if(c>0)
	    	System.out.println(">0");
	    else
	    	System.out.println("<=0");
	    //System.out.println("c "+Debug.getSymbolicIntegerValue(c));
	}
	public static void main(String[] args) {
		test(0,0);

	}

}
