package gov.nasa.jpf.symbc;


public class ExSymExeStrings52 {
	static int field;

  public static void main (String[] args) {
	  String a="aaa";
	  String b = "bbb";
	  String c = "ccc";
	  String d = "ddd";
	  test (a,b, 1);
	  Debug.printPC("This is the PC at the end:");
	  //a=a.concat(b);
	  
  }
  
  public static void test (String a, String b, int x) {
	  if (a.equals("aaa")) {
		  System.out.println("boo");
	  }
	  if (!a.equals("aaa")) {
		  System.out.println("aaa");
	  }
  }

}

