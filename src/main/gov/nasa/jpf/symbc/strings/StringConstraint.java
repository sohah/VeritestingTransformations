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

package gov.nasa.jpf.symbc.strings;

public class StringConstraint {
  private final StringExpression left;

  private final StringComparator comp;

  private final StringExpression right;

  StringConstraint and;

  public StringConstraint(StringExpression l, StringComparator c, StringExpression r) {
    left = l;
    comp = c;
    right = r;
  }

  /** Returns the left expression. Subclasses may override to give tighter type bounds.*/
  public StringExpression getLeft() {
      return left;
  }

  /** Returns the right expression. Subclasses may override to give tighter type bounds.*/
  public StringExpression getRight() {
      return right;
  }

  /**
   * Returns the comparator used in this constraint.
   */
  public StringComparator getComparator() {
    return comp;
  }

  /**
   * Returns the negation of this constraint, but without the tail.
   */
  public StringConstraint not() {
	  return new StringConstraint(getLeft(), getComparator().not(), getRight());
  }

  /**
   * Returns the next conjunct.
   */
  public StringConstraint getTail() {
    return and;
  }



  public boolean equals(Object o) {
    if (!(o instanceof StringConstraint)) {
      return false;
    }

    return left.equals(((StringConstraint) o).left)
        && comp.equals(((StringConstraint) o).comp)
        && right.equals(((StringConstraint) o).right);
  }

  public int hashCode() {
	  return left.hashCode() ^ comp.hashCode() ^ right.hashCode();
  }

  public String toString() {
    return left.toString() + comp.toString() + right.toString()
        + ((and == null) ? "" : " &&\n" + and.toString());
  }

  public StringConstraint last() {
      StringConstraint c= this;
      while(c.and != null) {
          c = c.and;
      }
      return c;
  }
}