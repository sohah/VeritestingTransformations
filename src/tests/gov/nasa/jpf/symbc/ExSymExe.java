package gov.nasa.jpf.symbc;


public class ExSymExe {
	static int field;

  public static void main (String[] args) {
	  int x = 3; /* we want to specify in an annotation that this param should be symbolic */

	  ExSymExe inst = new ExSymExe();
	  field = 9;
	  inst.test(x, field);
	  inst.test2(x,x);
  }
  /* we want to let the user specify that this method should be symbolic */

  public void test (int x, int z) {
	  //int y = 3;
	  x = z++ ;
	  //z=5;

	  if (z > 0) {
		 // assert(false);
		  System.out.println("branch FOO1");
	  }
	  else
		  System.out.println("branch FOO2");
	  if (x > 0)
		  System.out.println("branch BOO1");
	  else
		  System.out.println("branch BOO2");

	  //assert false;

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

