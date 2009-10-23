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

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.JVM;
import gov.nasa.jpf.jvm.MJIEnv;


// path condition contains constraints on strings

public class StringPathCondition {
    static boolean flagSolved = false;

    public StringConstraint header;
    int count = 0;


    public StringPathCondition() {
    	header = null;
    }

	public StringPathCondition make_copy() {
		StringPathCondition pc_new = new StringPathCondition();
		pc_new.header = this.header;
	    pc_new.count = this.count;
		return pc_new;
	}

	public void _addDet(StringComparator c, StringExpression l, String r) {
		flagSolved = false; // C
		_addDet(c, l, new StringConstant(r));
	}

	public void _addDet(StringComparator c, String l, StringExpression r) {
		flagSolved = false; // C
		_addDet(c, new StringConstant(l), r);
	}

	public void _addDet(StringComparator c, StringExpression l, StringExpression r) {

		StringConstraint t;
		flagSolved = false;
		t = new StringConstraint(l,c,r);
		prependUnlessRepeated(t);

	}



   /**
     * Prepends the given constraint to this path condition, unless the constraint is already included
     * in this condition.
     *
     * Returns whether the condition was extended with the constraint.
     */
    public boolean prependUnlessRepeated(StringConstraint t) {
        if (!hasConstraint(t)) {
            t.and = header;
            header = t;
            count++;
            return true;
        } else {
            return false;
        }
    }

    public void prependAllConjuncts(StringConstraint t) {
       t.last().and = header;
       header = t;
       count= length(header);
    }

    private static int length(StringConstraint c) {
        int x= 0;
        while (c != null) {
            x++;
            c = c.getTail();
        }
        return x;
    }

    /**
     * Returns the number of constraints in this path condition.
     */
	public int count() {
		return count;
	}

	/**
	 * Returns whether this path condition contains the constraint.
	 */
	public boolean hasConstraint(StringConstraint c) {
		StringConstraint t = header;

		while (t != null) {
			if (c.equals(t)) {
				return true;
			}

			t = t.and;
		}

		return false;
	}

	public void solve() {// TODO
	}

	public boolean simplify() { //TODO
		return true;
	}



	public String toString() {
		return "# = " + count + ((header == null) ? "" : "\n" + header.toString());
	}


}
