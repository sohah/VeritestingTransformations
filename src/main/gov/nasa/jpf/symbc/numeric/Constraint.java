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

import java.util.Map;

public abstract class Constraint {
  private final Expression left;

  private Comparator comp;

  private final Expression right;

  public Constraint and;

  public Constraint(Expression l, Comparator c, Expression r) {
    left = l;
    comp = c;
    right = r;
  }

  /** Returns the left expression. Subclasses may override to give tighter type bounds.*/
  public Expression getLeft() {
      return left;
  }

  /** Returns the right expression. Subclasses may override to give tighter type bounds.*/
  public Expression getRight() {
      return right;
  }

  /**
   * Returns the comparator used in this constraint.
   */
  public Comparator getComparator() {
    return comp;
  }

  public void setComparator(Comparator c) {
	    comp = c;
	  }
  /**
   * Returns the negation of this constraint, but without the tail.
   */
  public abstract Constraint not();

  /**
   * Returns the next conjunct.
   */
  public Constraint getTail() {
    return and;
  }

  public String stringPC() {
    return left.stringPC() + comp.toString() + right.stringPC()
        + ((and == null) ? "" : " && " + and.stringPC());
  }

  public void getVarVals(Map<String,Object> varsVals) {
	  if (left != null) {
		  left.getVarsVals(varsVals);
	  }
	  if (right != null) {
		  right.getVarsVals(varsVals);
	  }
	  if (and != null) {
		  and.getVarVals(varsVals);
	  }
  }

  public boolean equals(Object o) {
    if (!(o instanceof Constraint)) {
      return false;
    }

    return left.equals(((Constraint) o).left)
        && comp.equals(((Constraint) o).comp)
        && right.equals(((Constraint) o).right);
  }

  public int hashCode() {
	  int result = Integer.MAX_VALUE;
	  if (left != null) {
		  result = result ^ left.hashCode();
	  }
	  if (comp != null) {
		  result = result ^ comp.hashCode();
	  }
	  if (right != null) {
		  result = result ^ right.hashCode();
	  }
	  return result;
	  //return left.hashCode() ^ comp.hashCode() ^ right.hashCode();
  }

  public String toString() {
    return left.toString() + comp.toString() + right.toString()
        + ((and == null) ? "" : " &&\n" + and.toString());
  }

  public Constraint last() {
      Constraint c= this;
      while(c.and != null) {
          c = c.and;
      }
      return c;
  }
}