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

import gov.nasa.jpf.jvm.ChoiceGenerator;
import gov.nasa.jpf.jvm.JVM;
import gov.nasa.jpf.jvm.MJIEnv;
import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.string.StringPathCondition;

// path condition contains mixed constraints of integers and reals

public class PathCondition {
    static boolean flagSolved = false;
    //neha: additional check to control when
    // constraints need to be solve
    public static boolean flagCheck = true;

    public Constraint header;
    int count = 0;

    // TODO: to review
    public StringPathCondition spc = new StringPathCondition(this);

    public PathCondition() {
    	header = null;
    }

	public PathCondition make_copy() {
		PathCondition pc_new = new PathCondition();
		pc_new.header = this.header;
	    pc_new.count = this.count;
	    pc_new.spc = this.spc.make_copy(pc_new); // TODO: to review
		return pc_new;
	}


	public void _addDet(Comparator c, Expression l, Expression r) {
		if (l instanceof IntegerExpression && r instanceof IntegerExpression)
			_addDet(c,(IntegerExpression)l,(IntegerExpression)r);
		else if (l instanceof RealExpression && r instanceof RealExpression)
			_addDet(c,(RealExpression)l,(RealExpression)r);
		else
			throw new RuntimeException("## Error: _addDet (type incompatibility real/integer) " + c + " " + l + " " + r);

	}

	// constraints on integers
	public void _addDet(Comparator c, IntegerExpression l, int r) {
		flagSolved = false; // C
		_addDet(c, l, new IntegerConstant(r));
	}

	public void _addDet(Comparator c, int l, IntegerExpression r) {
		flagSolved = false; // C
		_addDet(c, new IntegerConstant(l), r);
	}

	public void _addDet(Comparator c, IntegerExpression l, long r) {
		flagSolved = false; // C
		_addDet(c, l, new IntegerConstant((int)r));
		//_addDet(c, l, (int)r);
	}

	public void _addDet(Comparator c, long l, IntegerExpression r) {
		flagSolved = false; // C
		_addDet(c, new IntegerConstant((int)l), r);
		//_addDet(c, (int)l, r);
	}

	public void _addDet(Comparator c, IntegerExpression l, IntegerExpression r) {

		Constraint t;
		flagSolved = false;
		if ((l instanceof LinearIntegerExpression) && (r instanceof LinearIntegerExpression)) {
			t = new LinearIntegerConstraint(l, c, r);
		} else {
			t = new NonLinearIntegerConstraint(l, c, r);
		}

		prependUnlessRepeated(t);

	}


	// constraints on reals
	public void _addDet(Comparator c, RealExpression l, double r) {
		flagSolved = false; // C
		_addDet(c, l, new RealConstant(r));
	}

	public void _addDet(Comparator c, double l, RealExpression r) {
		flagSolved = false; // C
		_addDet(c, new RealConstant(l), r);
	}

	public void _addDet(Comparator c, RealExpression l, RealExpression r) {
		Constraint t;

		flagSolved = false; // C

		t = new RealConstraint(l, c, r);

		prependUnlessRepeated(t);

	}

//	mixed real/integer constraints to handle cast bytecodes

	public void _addDet(Comparator c, RealExpression l, IntegerExpression r) {
		Constraint t;

		flagSolved = false; // C

		t = new MixedConstraint(l, c, r);

		prependUnlessRepeated(t);

	}

	public void _addDet(Comparator c, IntegerExpression l, RealExpression r) {
		Constraint t;

		flagSolved = false; // C

		t = new MixedConstraint(r, c, l);

		prependUnlessRepeated(t);

	}

   /**
     * Prepends the given constraint to this path condition, unless the constraint is already included
     * in this condition.
     *
     * Returns whether the condition was extended with the constraint.
     */
    public boolean prependUnlessRepeated(Constraint t) {
        if (!hasConstraint(t)) {
            t.and = header;
            header = t;
            count++;
            return true;
        } else {
            return false;
        }
    }

    public void prependAllConjuncts(Constraint t) {
       t.last().and = header;
       header = t;
       count= length(header);
    }

    private static int length(Constraint c) {
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
	public boolean hasConstraint(Constraint c) {
		Constraint t = header;

		while (t != null) {
			if (c.equals(t)) {
				return true;
			}

			t = t.and;
		}

		return false;
	}

	public void solve() {// warning: solve calls simplify

		SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
		solver.solve(this);
		PathCondition.flagSolved = true;

		// modification for string path condition
		spc.solve(); // TODO: to review
	}

	public boolean simplify() {
		//neha: Added this to control solving the path constraint
		// contingent on the variable being set.
//		if (!PathCondition.flagCheck){
//			return true;
//		}

		SymbolicConstraintsGeneral solver = new SymbolicConstraintsGeneral();
		boolean result1 = solver.isSatisfiable(this);
		
		if (SymbolicInstructionFactory.debugMode) {
			MinMax.Debug_no_path_constraints ++;
			if (result1)
				MinMax.Debug_no_path_constraints_sat ++;
			else
				MinMax.Debug_no_path_constraints_unsat ++;
			System.out.println("### PCs: " + MinMax.Debug_no_path_constraints + " " +MinMax.Debug_no_path_constraints_sat + " " + MinMax.Debug_no_path_constraints_unsat);
		}

		if (! result1) return false;
		boolean result2 = spc.simplify(); // TODO to review: used for strings
		return result1  && result2;
	}

	public String stringPC() {
		return "# = " + count + ((header == null) ? "" : "\n" + header.stringPC())
		            + "\n" + spc.stringPC(); // TODO: to review
	}

	public String toString() {
		return "# = " + count + ((header == null) ? "" : "\n" + header.toString())
					+ "\n" + spc.toString(); // TODO: to review
	}

	public static PathCondition getPC(MJIEnv env) {
	   JVM vm = env.getVM();
	   return getPC(vm);
	}

	public static PathCondition getPC(JVM vm) {
	    ChoiceGenerator<?> cg = vm.getChoiceGenerator();
	    if (cg != null && !(cg instanceof PCChoiceGenerator)) {
	        cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);
	    }

	    if (cg instanceof PCChoiceGenerator) {
	        return ((PCChoiceGenerator) cg).getCurrentPC();
	    } else {
	        return null;
	    }
	}

}
