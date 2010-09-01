package gov.nasa.jpf.symbc;


public class ExSymExeStrings21 {
	static int field;

  public static void main (String[] args) {
	  String a="aaa";
	  String b = "bbb";
	  String c = "ccc";
	  test (a,b, c);
	  Debug.printPC("This is the PC at the end:");
	  //a=a.concat(b);
	  
  }
  
  public static void test (String a, String b, String c) {
	  if (a.equals(b)) {
		  System.out.println("aaa");
	  }
	  if (b.equals(c)) {
		  System.out.println("bbb");
	  }

  }

}

