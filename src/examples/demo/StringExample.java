package demo;

import gov.nasa.jpf.symbc.Debug;

public class StringExample {
	
	public static void main (String[] args) {
		System.out.println("start");
		test("<<<<<a href=\">    @");
		System.out.println ("end");
	}
	
	public static void test(String body) {
		if (body == null)
			return;
		int len = body.length();
		for(int i=0; i< len; i++) 
			if (body.charAt(i) != '<') 
				return;
		System.out.println("false "+Debug.getSymbolicStringValue(body));
		assert false;
	}
}