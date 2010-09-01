/*  Copyright (C) 2005 United States Government as represented by the
Administrator of the National Aeronautics and Space Administration
(NASA).  All Rights Reserved.

Copyright (C) 2009 Fujitsu Laboratories of America, Inc.

DISCLAIMER OF WARRANTIES AND LIABILITIES; WAIVER AND INDEMNIFICATION

A. No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY
WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY,
INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE
WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM
INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR
FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO
THE SUBJECT SOFTWARE. NO SUPPORT IS WARRANTED TO BE PROVIDED AS IT IS PROVIDED "AS-IS".

B. Waiver and Indemnity: RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS
AGAINST FUJITSU LABORATORIES OF AMERICA AND ANY OF ITS AFFILIATES, THE
UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL
AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE
RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING
FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING
FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY
AND HOLD HARMLESS FUJITSU LABORATORTIES OF AMERICA AND ANY OF ITS AFFILIATES,
THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL
AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE
REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL
TERMINATION OF THIS AGREEMENT.

*/

package gov.nasa.jpf.symbc.string;

import java.util.HashMap;
import java.util.Map;

import gov.nasa.jpf.symbc.mixednumstrg.*;

import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.MinMax;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;


public abstract class StringExpression extends Expression {

  SymbolicInteger length = null;
  Map<String, SymbolicCharAtInteger> charAt = null;
  Map<StringExpression, SymbolicIndexOfInteger> indexOf = null;

//   protected StringDependentNode dependentsHead = null;
//   protected StringRelationshipNode relationshipsHead = null;

/* length */
  static int lengthcount = 0;
  
  public IntegerExpression _charAt (IntegerExpression ie) {
	  if (charAt == null) {
		  charAt = new HashMap<String, SymbolicCharAtInteger>();
	  }
	  SymbolicCharAtInteger result = charAt.get(ie.toString());
	  if (result == null) {
		  result = new SymbolicCharAtInteger("CharAt(" + ie.toString() + ")_" + lengthcount + "_", 0, MinMax.MAXINT, this, ie);
		  lengthcount++;
		  charAt.put(ie.toString(), result);
	  }
	  return result;
  }
  
  public IntegerExpression _length() {
    if (length == null) {
      length = new SymbolicLengthInteger("Length_" + lengthcount + "_", 1, MinMax.MAXINT, this);
      lengthcount++;
    }
    return length;
  }

/* indexOf */
  public IntegerExpression _indexOf(StringExpression exp) {
	    if (indexOf == null) {
	      indexOf = new HashMap<StringExpression, SymbolicIndexOfInteger>();
	    }
	    SymbolicIndexOfInteger sioi = indexOf.get(exp);
	    if (sioi == null) {
	    	//-1 Should make our lifes much easier
	    	sioi = new SymbolicIndexOfInteger("IndexOf_" + lengthcount + "_", -1, MinMax.MAXINT, this, exp);
	    	lengthcount++;
	    	indexOf.put(exp, sioi);
	    }
	    return sioi;
	  }

  /* trim */
  public StringExpression _trim() {
    return new DerivedStringExpression(StringOperator.TRIM, this);
  }

/* concat */
  public StringExpression _concat(String s) {
    return new DerivedStringExpression(this, StringOperator.CONCAT, new StringConstant(s));
  }

  public StringExpression _concat(StringExpression e) {
    return new DerivedStringExpression(this, StringOperator.CONCAT, e );
  }

  public StringExpression _concat(IntegerExpression e) {
	    return new DerivedStringExpression(this, StringOperator.CONCAT, _valueOf(e) );
	  }


  public StringExpression _concat(RealExpression e) {
	    return new DerivedStringExpression(this, StringOperator.CONCAT, _valueOf(e));
	  }

 /* replace */

  public StringExpression _replace(StringExpression t, StringExpression r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = t;
	    l[2] = r;
	    return new DerivedStringExpression(StringOperator.REPLACE, l );
	  }

  public StringExpression _replace(String t, StringExpression r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = new StringConstant(t);
	    l[2] = r;
	    return new DerivedStringExpression(StringOperator.REPLACE, l );
	  }

  public StringExpression _replace(String t, String r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = new StringConstant(t);
	    l[2] = new StringConstant(r);
	    return new DerivedStringExpression(StringOperator.REPLACE, l );
	  }

  public StringExpression _replace(StringExpression t, String r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = t;
	    l[2] = new StringConstant(r);
	    return new DerivedStringExpression(StringOperator.REPLACE, l );
	  }

  /* subString */

  public StringExpression _subString(IntegerExpression t, int r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = t;
	    l[2] = new IntegerConstant(r);
	    return new DerivedStringExpression(StringOperator.SUBSTRING, l );
	  }

  public StringExpression _subString(IntegerExpression t, IntegerExpression r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = t;
	    l[2] = r;
	    return new DerivedStringExpression(StringOperator.SUBSTRING, l );
	  }

public StringExpression _subString(Integer t, IntegerExpression r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = new IntegerConstant(t);
	    l[2] = r;
	    return new DerivedStringExpression(StringOperator.SUBSTRING, l );
	  }

public StringExpression _subString(int t, int r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = new IntegerConstant(t);
	    l[2] = new IntegerConstant(r);
	    return new DerivedStringExpression(StringOperator.SUBSTRING, l );
	  }

public StringExpression _subString(int t) {
    Expression l[] = new Expression[2];
    l[0] = this;
    l[1] = new IntegerConstant(t);
    return new DerivedStringExpression(StringOperator.SUBSTRING, l );
  }

public StringExpression _subString(IntegerExpression t) {
    Expression l[] = new Expression[2];
    l[0] = this;
    l[1] = t;
    return new DerivedStringExpression(StringOperator.SUBSTRING, l );
  }

/* Replace First */

  public StringExpression _replaceFirst(StringExpression t, StringExpression r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = t;
	    l[2] = r;
	    return new DerivedStringExpression(StringOperator.REPLACEFIRST, l );
	  }

public StringExpression _replaceFirst(String t, StringExpression r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = new StringConstant(t);
	    l[2] = r;
	    return new DerivedStringExpression(StringOperator.REPLACEFIRST, l );
	  }

public StringExpression _replaceFirst(String t, String r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = new StringConstant(t);
	    l[2] = new StringConstant(r);
	    return new DerivedStringExpression(StringOperator.REPLACEFIRST, l );
	  }

public StringExpression _replaceFirst(StringExpression t, String r) {
	    Expression l[] = new Expression[3];
	    l[0] = this;
	    l[1] = t;
	    l[2] = new StringConstant(r);
	    return new DerivedStringExpression(StringOperator.REPLACEFIRST, l );
	  }

/* valueOf */

public static StringExpression _valueOf(IntegerExpression t) {
        Expression l[] = new Expression[1];
	    l[0] = t;
	    return new DerivedStringExpression(StringOperator.VALUEOF, l );
}

public static StringExpression _valueOf(RealExpression t) {
    Expression l[] = new Expression[1];
    l[0] = t;
    return new DerivedStringExpression(StringOperator.VALUEOF, l );
}

public static StringExpression _valueOf(StringExpression t) {
    Expression l[] = new Expression[1];
    l[0] = t;
    return new DerivedStringExpression(StringOperator.VALUEOF, l );
}

public IntegerExpression _IvalueOf() {
	return new SpecialIntegerExpression(this);
}

public RealExpression _RvalueOf() {
	return new SpecialRealExpression(this);
}

  public static String _toString(StringExpression s) {
	    return s.toString();
	  }

  public String _formattedToString() {
	    if (this instanceof StringConstant) {
	      return "\"" + toString() + "\"";
	    }
	    return toString();
	  }

  public String getName() {
    return "STRING_" + hashCode();
  }


  //TODO test this
  public String solution() {
    throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
  }

  public StringExpression clone() {return clone();}

//    public static class StringDependentNode {
//	    StringDependentNode next;
//	    DerivedStringExpression dependent;
//
//	    public StringDependentNode (DerivedStringExpression d) {
//	      dependent = d;
//	    }
//
//	    public boolean equals (Object o) {
//	      if (!(getClass().equals(o.getClass()))) {
//	        return false;
//	      }
//
//	      return dependent.equals(((StringDependentNode) o).dependent);
//	    }
//	  }
//
//     public static class StringRelationshipNode {
//	    StringRelationshipNode next;
//	    StringConstraint relationship;
//
//	    public StringRelationshipNode(StringConstraint d) {
//	      relationship = d;
//	    }
//
//	    public boolean equals(Object o) {
//	      if (!(getClass().equals(o.getClass()))) {
//	        return false;
//	      }
//
//	      return relationship.equals(((StringRelationshipNode) o).relationship);
//	    }
//	  }
//
//      public void addDependent(DerivedStringExpression e) {
//	    StringDependentNode n = new StringDependentNode(e);
//	    n.next = dependentsHead;
//	    dependentsHead = n;
//	  }
//
//
//	  public void addRelationship(StringConstraint c) {
//	    StringRelationshipNode n = new StringRelationshipNode(c);
//	    n.next = relationshipsHead;
//	    relationshipsHead = n;
//	  }


}


