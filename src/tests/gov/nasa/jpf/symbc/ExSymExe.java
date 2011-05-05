package gov.nasa.jpf.symbc;


public class ExSymExe {
	static int field;

  public static void main (String[] args) {
	  int x = 3; /* we want to specify in an annotation that this param should be symbolic */

	  ExSymExe inst = new ExSymExe();
	  field = 9;
	  //inst.test(0, 1);
	  //inst.test2(x,x);
	  //inst.test1(x,true);
	  //inst.test3(0.0, 0.0);
	  inst.test4(0.0, 0);
	  inst.test5(0.0, 0);
  }
  /* we want to let the user specify that this method should be symbolic */
  public void test5(double xm, double ym) {
	  if(ym == (1.0 + xm) && (ym - xm) == (3.0 + ym))
		 System.out.println("true");
	  else
		 System.out.println("false");
  }

  public void test3(double x, double y) {
	  if(Math.sin(x)+Math.cos(y)==1)
		  System.out.println("eq");
	  else
		  System.out.println("neq");

	  System.out.println("1. <1"+(Math.sin(-10000.0)+Math.cos(-10000.0)));
	  System.out.println("2. ==1"+(Math.sin(-10000.0)+Math.cos(-9998.118620049521)));
	  System.out.println("3. >1"+(Math.sin(-10000.0)+Math.cos(-9998.118619049521)));
  }

  public void test4(double x, int y) {
	  if(x+y==0)
		  System.out.println("eq");
	  else
		  System.out.println("neq");
  }


  public void test1 (int x, boolean b) {
	  Integer z = new Integer(x);
	  if (z <= 1200)
		  System.out.println("le 1200");
	  if(z >= 1200)
		  System.out.println("ge 1200");
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

