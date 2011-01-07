package concolic;

import gov.nasa.jpf.symbc.Concrete;
import gov.nasa.jpf.symbc.Partition;

public class MathSin {

/*
#define IEEE_BIAS       1023
#define IEEE_MAX        2047
#define IEEE_MANT       52
#define IEEE_EBIT       (1L<<20)

*/

public static final int IEEE_MAX = 2047;
public static final int IEEE_BIAS = 1023;
public static final int IEEE_MANT = 52;
public static final double sixth = 1.0/6.0;
public static final double half = 1.0/2.0;
public static final double mag52 = 1024.*1024.*1024.*1024.*1024.*4.;/*2**52*/
public static final double magic = 1024.*1024.*1024.*1024.*1024.*4.;/*2**52*/

	public static final double[] P = { 
		  -0.64462136749e-9,
		   0.5688203332688e-7,
		  -0.359880911703133e-5,
		   0.16044116846982831e-3,
		  -0.468175413106023168e-2,
		   0.7969262624561800806e-1,
		  -0.64596409750621907082,
		   0.15707963267948963959e1
		 };
	
public static double _2_pi_hi;
public static double pi2_lo;
public static double pi2_hi_hi;
public static double pi2_hi_lo;
public static double pi2_lo_hi;
public static double pi2_lo_lo;
public static double pi2_hi;
public static double pi2_lo2;

public static final double X_EPS = 1e-10;


public static double a2, c1, c2;
	
@Concrete("true")
@Partition({"x>=0.0&&x<=1.0","x==1.0E-55"})
public static double calculate(double x){

	double retval;
	double x_org;
	double x2;

	int md_b_sign;
	int xexp;
	int sign=0;
	int md_b_m1;
	int md_b_m2;

	System.out.println(">>>> input "+x);
	// convert into the different parts
	//
	long l_x = Double.doubleToRawLongBits(x);
	//System.out.println("raw"+l_x);
	md_b_sign = (int) ((l_x >> 63) & 1);
	xexp = (int)((l_x >> 52) & 0x7FF);
	//System.out.println("exp raw"+xexp);

	// introduce sign of exponent
	if (xexp > 0x400){
		xexp = - (xexp &0x3ff);
	}
	md_b_m2 = (int)(l_x & 0xFFFFFFFF);
	md_b_m1 = (int)((l_x >> 31) & 0xFFFFF);
	System.out.println("sign="+md_b_sign);
	System.out.println("exp="+xexp);
	System.out.println("exp (unbiased)="+(xexp-IEEE_BIAS));
	System.out.println("m1="+md_b_m1);
	System.out.println("m2="+md_b_m2);

	if (IEEE_MAX == xexp){
		if( md_b_m1 >0 || md_b_m2 >0  ){
			System.out.println("unnormalized");
			retval = x; 
		}else{   
			System.out.println("NaN");
			retval = Double.NaN;
		}
		return retval;
	}
	else if (0 == xexp){
		System.out.println("exp==0");
		return xexp;
	} else if (xexp < (IEEE_BIAS - IEEE_MANT - 2)){
		System.out.println("very small");
		return x;
	}else if( xexp <= (IEEE_BIAS - IEEE_MANT/4) ){ /* small x       */
		System.out.println("small");
		return x*(1.0-x*x*sixth); /* x**4 < epsilon of x        */
	}
	// 


	if (md_b_sign == 1){
		x = -x;
		sign = 1;
	}
	x_org = x;
	if (xexp < IEEE_BIAS){
		System.out.println("<1");
		;
	}else if (xexp <= (IEEE_BIAS + IEEE_MANT)){
		System.out.println("must bring into range...");
		double xm, x3, x4, x5, x6;
		// SKIPPED int bot2;  
		double xn_d;
		double md; // should be bit union

		// xm = (x * _2_pi_hi + magic) - magic;
		xm = Math.floor(x * _2_pi_hi + half);     // should be: floor(....)
		xn_d = xm + mag52;

		// bot2 is the lower 3 bits of M2
		long l_xn = Double.doubleToRawLongBits(xn_d);

		// md_b_sign = (int) ((l_x >> 64) & 1);
		// xexp = (int)((l_x >> 1) & 0x7FF);
		int xn_m2 = (int)(l_xn & 0xFFFFFFFF);

		int bot2 = xn_m2 & 3;


		// SKIPPED: bot2 now input bot2 = (int)xm;   // should be: xn.b.m2 & 3; 

		/*
		 * Form xm * (pi/2) exactly by doing:
		 *      (x3,x4) = xm * pi2_hi
		 *      (x5,x6) = xm * pi2_lo
		 */
		// split(a1,a2,xm);
		// exactmul2(x3,x4, xm,a1,a2, pi2_hi,pi2_hi_hi,pi2_hi_lo);
		// exactmul2(x5,x6, xm,a1,a2, pi2_lo,pi2_lo_hi,pi2_lo_lo);
		// x = ((((x - x3) - x4) - x5) - x6) - xm*pi2_lo2; /* x - m*(pi/2) */

		// should be : md.d = (xm); md.b.m2 &= 0xfc000000u; a1 = md.d; a2 = (xm) - a1;;
		// x3 = (xm)*(pi2_hi); x4 = (((a1*pi2_hi_hi-x3)+a1*pi2_hi_lo)+pi2_hi_hi*a2)+a2*pi2_hi_lo;;
		// x5 = (xm)*(pi2_lo); x6 = (((a1*pi2_lo_hi-x5)+a1*pi2_lo_lo)+pi2_lo_hi*a2)+a2*pi2_lo_lo;;
		//  x = ((((x - x3) - x4) - x5) - x6) - xm*pi2_lo2;

		long l_xm = Double.doubleToRawLongBits(xm);

		//int xm_sign = (int) ((l_x >> 64) & 1);
		//int xm_xexp = (int)((l_x >> 1) & 0x7FF);
		int xm_b_m2 = (int)(l_x & 0xFFFFFFFF);

		xm_b_m2 = xm_b_m2 & 0xfc000000;
		l_xm = l_xm & (0xffffffff00000000L);
		l_xm = l_xm & xm_b_m2;
		double a1 = Double.longBitsToDouble(l_xm);

		// SKIPPED: a1 as input: a1 = md;
		a2 = (xm) - a1;;

		x3 = (xm)*(pi2_hi); x4 = (((a1*pi2_hi_hi-x3)+a1*pi2_hi_lo)+pi2_hi_hi*a2)+a2*pi2_hi_lo;;
		x5 = (xm)*(pi2_lo); x6 = (((a1*pi2_lo_hi-x5)+a1*pi2_lo_lo)+pi2_lo_hi*a2)+a2*pi2_lo_lo;;
		x = ((((x - x3) - x4) - x5) - x6) - xm*pi2_lo2;




		switch(bot2){
		case 0:
			if (x < 0.0) {
				x = -x;
				//sign ^= 1;
				if (sign ==1)
					sign = 0;
				else
					sign = 1;
			}
			break;
		case 1:
			if( x < 0.0 ){
				x = pi2_hi + x;
			}else{
				x = pi2_hi - x;
			}
			break;
		case 2:
			if (x < 0.0) {
				x = -x;
			}else{

				//sign ^= 1;
				if (sign ==1)
					sign = 0;
				else
					sign = 1;
			}
			break;
		case 3:
			// sign ^= 1;
			if (sign ==1)
				sign = 0;
			else
				sign = 1;

			if( x < 0.0 ){
				x = pi2_hi + x;
			}else{
				x = pi2_hi - x;
			}
			break;
		default:;
		}
	}else {
		System.out.println("return: exp > BIAS+MANT ");
		retval = 0.0;
		if (sign == 1)
			retval = -retval;
		return retval;
	}

	x = x * _2_pi_hi;


	if (x > X_EPS){
		x2 = x*x;
		// x *= __POL7(P,x2);
		// #define __POL7(C,X)     __POL(C,X,7)
		// in math1.h
		// 
		x *= ((((((((P)[0]*(x2) + (P)[1])*(x2) + 
				(P)[2])*(x2) + (P)[3])*(x2) + (P)[4])*(x2) + (P)[5])*(x2) + (P)[6])*(x2) + (P)[7]);
	}else 
		x *= pi2_hi;              /* x = x * (pi/2)               */

	if (sign==1) x = -x;
	System.out.println("final return");
	return x;
}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
	    MathSin.calc(1.0);
	   
	  //  double x = MathSin.calculate(0.0);
     //  System.out.println("0 -->" + x);
     //  System.out.println("1e-55 --> "+ MathSin.calculate(1e-55)); //1.0E-55
     //  System.out.println("1e-1 -->"+ MathSin.calculate(1e-1)); // 0.0
     //  System.out.println("1 -->"+ MathSin.calculate(1.0)); // 0.0
    //   System.out.println("0.12 -->" + MathSin.calculate(1.2));
      //  Debug.printPC("\nMathSin.calculate Path Condition: ");

	}
	
	public static void calc(double x) {
		 if(MathSin.calculate(x) == 0) {
		    	System.out.println("value of 0.0 ----- br1 !!!!!!!!!!!!!!!!!!!");
		 } 
		  if(MathSin.calculate(x) == 1.0E-55) {
		    	System.out.println("\n value of 1e-55 ----- br2 !!!!!!!!!!!!!!!!!!");
		 }
	}
}

