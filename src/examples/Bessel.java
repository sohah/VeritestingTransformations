import gov.nasa.jpf.symbc.Concrete;

// The Bessel.java file

public class Bessel
{

  // Declaration of the Native (C) function
  public static native double bessely0(double x);

  static
    {
	  //System.setProperty("java.library.path","/Users/nrungta/Documents/sandbox/bassel/lib");
	  // The runtime system executes a class's static
      // initializer when it loads the class.
      System.loadLibrary("CJavaInterface"); 
    }

  // Create an object of class Bessel
  static Bessel bess = new Bessel();  

  // The main program
  public static void main(String[] args)
    {
      double x, y;
      int i;

      /* Check that we've been given an argument */
      if (args.length != 1)
        {
          System.out.println("Usage: java Bessel x");
          System.out.println("       Computes Y0 Bessel function of argument x");
          System.exit(1);
        }

      /* Convert the command line argument to a double */
      x = new Double(args[0]).doubleValue();
      run(x); 
     
    }
  
  public static void run(double x) {
	  System.out.println();
      System.out.println("Calls of Y0 Bessel function routine bessely0");
      double y = 0.0;
     // for (i = 0; i < 10; i++)
    //    {
          /* Call method bessely0 of object bess */
          y = y0(x) /* bess.bessely0(x);*/;
          /* Increase x and repeat */
    //      System.out.println("coming here i :" + i);
         
        	 // System.out.println("y");
          //}
          //x = x + 0.25;
//        }
      if(x> 0 && y < 1.0) {
    	  System.out.println("xxxxxxxx");
      } //else {
  }
  
  @Concrete("true")
  public static double y0(double x) {
	  return bess.bessely0(x);
  }
}
