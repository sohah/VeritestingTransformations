package gov.nasa.jpf.symbc;


public class ExSymExe {
	static int field;

  public static void main (String[] args) {
	  int x = 3; /* we want to specify in an annotation that this param should be symbolic */

	  ExSymExe inst = new ExSymExe();
	  field = 9;
	  //inst.test(0, 1);
	  //inst.test2(x,x);
	  inst.test1(x,true);
  }
  /* we want to let the user specify that this method should be symbolic */

  public void test1 (int x, boolean b) {
	  Integer z = new Integer(x);
	  if (z <= 1200)
		  System.out.println("le 0");
	  if(z >= 1200)
		  System.out.println("ge 0");
	  if(b)
		  System.out.println("b true");
	  else
		  System.out.println("b false");
	 //assert (false);
  }
  public void test (int x, int z) {
	  if (x > z)
		  if (z > x)
			  System.out.println("unreachable");
	  if (x/6 > 0)
		  System.out.println("br1");
	  else
		  System.out.println("br2");
  }
  public void test2 (int x, int z) {
	  System.out.println("in test2 "+ x + " " +z);
	  x = z++ ;
	  //z=5;
	  if (z > 0) {
		  //assert (false);
		  System.out.println("branch2 FOO1");
	  }
	  else
		  System.out.println("branch2 FOO2");
	  if (x > 0)
		  System.out.println("branch2 BOO1");
	  else
		  System.out.println("branch2 BOO2");

	  //assert false;

  }
}

