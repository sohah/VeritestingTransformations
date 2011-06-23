//
//Copyright (C) 2006 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.
//
//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.
//
//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//

package gov.nasa.jpf.symbc.numeric;

public class MinMax {
	public static int MININT = -1000000;//Integer.MIN_VALUE;//-10000;
	public static int MAXINT = 1000000;// Integer.MAX_VALUE;//10000;
	public static double MINDOUBLE = -10000.0;//-1.0e8;//Double.MIN_VALUE;
	public static double MAXDOUBLE = 10000.0;//1.0e8; //Double.MAX_VALUE;

	public static int Debug_no_path_constraints = 0;
	public static int Debug_no_path_constraints_sat = 0;
	public static int Debug_no_path_constraints_unsat = 0;

	public static int UniqueId = 0; // Unique id for each SymbolicInteger or SymbolicReal created
	
	public static void reset() {
	  UniqueId = 0;
	}
}
