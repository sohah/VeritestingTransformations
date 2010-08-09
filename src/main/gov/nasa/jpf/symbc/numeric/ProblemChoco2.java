package gov.nasa.jpf.symbc.numeric;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;

/**
 * Integration of the Choco CP library version 2 (2.1.1, specifically).
 * Currently only supports integer operations.
 *
 * @author staats
 *
 */

public class ProblemChoco2 extends ProblemGeneral {
	private CPSolver solver;
	private Model model;

	public ProblemChoco2() {
		model = new CPModel();
		solver = new CPSolver();
	}

	Object and(int value, Object exp) {	throw new RuntimeException("## Unsupported and "); }
	Object and(Object exp, int value) {	throw new RuntimeException("## Unsupported and "); }
	Object and(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported and "); }

	Object div(int value, Object exp) { return Choco.div(value, (IntegerExpressionVariable) exp); }
	Object div(Object exp, int value) { return Choco.div((IntegerExpressionVariable) exp, value); }
	Object div(Object exp1, Object exp2) { return Choco.div((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object div(double value, Object exp) {	throw new RuntimeException("## Unsupported double div "); }
	Object div(Object exp, double value) {	throw new RuntimeException("## Unsupported double div "); }

	Object eq(int value, Object exp) { return Choco.eq(value, (IntegerExpressionVariable) exp);	}
	Object eq(Object exp, int value) { return Choco.eq((IntegerExpressionVariable) exp, value);	}
	Object eq(Object exp1, Object exp2) { return Choco.eq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp1);	}

	Object eq(double value, Object exp) {	throw new RuntimeException("## Unsupported eq "); }
	Object eq(Object exp, double value) {	throw new RuntimeException("## Unsupported eq "); }

	Object geq(int value, Object exp) { return Choco.geq(value, (IntegerExpressionVariable) exp);	}
	Object geq(Object exp, int value) { return Choco.geq((IntegerExpressionVariable) exp, value);	}
	Object geq(Object exp1, Object exp2) { return Choco.geq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp1);	}

	Object geq(double value, Object exp) {	throw new RuntimeException("## Unsupported geq "); }
	Object geq(Object exp, double value) {	throw new RuntimeException("## Unsupported geq "); }

	int getIntValue(Object dpVar) {
		try {
			return solver.getVar((IntegerVariable) dpVar).getVal(); 
		} catch (Throwable t) {
			return ((IntegerVariable) dpVar).getLowB();
		}
	}

	double getRealValue(Object dpVar) {	throw new RuntimeException("## Unsupported get real value "); }
	double getRealValueInf(Object dpvar) {	throw new RuntimeException("## Unsupported get real value "); }
	double getRealValueSup(Object dpVar) {	throw new RuntimeException("## Unsupported get real value "); }

	Object gt(int value, Object exp) { return Choco.gt(value, (IntegerExpressionVariable) exp); }
	Object gt(Object exp, int value) { return Choco.gt((IntegerExpressionVariable) exp, value); }
	Object gt(Object exp1, Object exp2) { return Choco.gt((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object gt(double value, Object exp) {	throw new RuntimeException("## Unsupported double gt "); }
	Object gt(Object exp, double value) {	throw new RuntimeException("## Unsupported double gt "); }

	Object leq(int value, Object exp) { return Choco.leq(value, (IntegerExpressionVariable) exp); }
	Object leq(Object exp, int value) { return Choco.leq((IntegerExpressionVariable) exp, value); }
	Object leq(Object exp1, Object exp2) { return Choco.leq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object leq(double value, Object exp) {	throw new RuntimeException("## Unsupported double leq "); }
	Object leq(Object exp, double value) {	throw new RuntimeException("## Unsupported double leq "); }

	Object lt(int value, Object exp) { return Choco.lt(value, (IntegerExpressionVariable) exp); }
	Object lt(Object exp, int value) { return Choco.lt((IntegerExpressionVariable) exp, value); }
	Object lt(Object exp1, Object exp2) { return Choco.lt((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object lt(double value, Object exp) {	throw new RuntimeException("## Unsupported double lt "); }
	Object lt(Object exp, double value) {	throw new RuntimeException("## Unsupported double lt "); }

	Object makeIntVar(String name, int min, int max) {
		return Choco.makeIntVar(name, min, max);
	}

	Object makeRealVar(String name, double min, double max) {	throw new RuntimeException("## Unsupported make real "); }

	Object minus(int value, Object exp) { return Choco.minus(value, (IntegerExpressionVariable) exp); }
	Object minus(Object exp, int value) { return Choco.minus((IntegerExpressionVariable) exp, value); }
	Object minus(Object exp1, Object exp2)  { return Choco.minus((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object minus(double value, Object exp) {	throw new RuntimeException("## Unsupported double minus "); }
	Object minus(Object exp, double value) {	throw new RuntimeException("## Unsupported double minus "); }
	Object mixed(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported mixed "); }

	Object mult(int value, Object exp) { return Choco.mult(value, (IntegerExpressionVariable) exp); }
	Object mult(Object exp, int value) { return Choco.mult((IntegerExpressionVariable) exp, value); }
	Object mult(Object exp1, Object exp2)  { return Choco.mult((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object mult(double value, Object exp) {	throw new RuntimeException("## Unsupported double mult "); }
	Object mult(Object exp, double value) {	throw new RuntimeException("## Unsupported double mult "); }

	Object neq(int value, Object exp) { return Choco.neq(value, (IntegerExpressionVariable) exp); }
	Object neq(Object exp, int value) { return Choco.neq((IntegerExpressionVariable) exp, value); }
	Object neq(Object exp1, Object exp2)  { return Choco.neq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object neq(double value, Object exp) {	throw new RuntimeException("## Unsupported double NEQ "); }
	Object neq(Object exp, double value) {	throw new RuntimeException("## Unsupported double NEQ "); }

	Object or(int value, Object exp) {	throw new RuntimeException("## Unsupported OR "); }
	Object or(Object exp, int value) {	throw new RuntimeException("## Unsupported OR "); }
	Object or(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported OR "); }

	Object plus(int value, Object exp) { return Choco.plus(value, (IntegerExpressionVariable) exp); }
	Object plus(Object exp, int value) { return Choco.plus((IntegerExpressionVariable) exp, value); }
	Object plus(Object exp1, Object exp2)  { return Choco.plus((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }

	Object plus(double value, Object exp) {	throw new RuntimeException("## Unsupported double plus "); }
	Object plus(Object exp, double value) {	throw new RuntimeException("## Unsupported double plus "); }

	void post(Object constraint) {
		model.addConstraint((Constraint) constraint);
	}

	Object shiftL(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftL"); }
	Object shiftL(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftL"); }
	Object shiftL(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftL"); }

	Object shiftR(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftR"); }
	Object shiftR(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftR"); }
	Object shiftR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftR"); }

	Object shiftUR(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftUR"); }
	Object shiftUR(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftUR"); }
	Object shiftUR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftUR"); }

	/*
	 * One potential issue is determining the best way to build constraints.
	 * Currently the model is reset after solving, and the solver
	 * is reset right before solving. Is this the best way to do this?
	 * We could alternatively pop constraints when backtracking,
	 * though this would require some changes to how ProblemGeneral
	 * is interfaced.
	 *
	 */
	Boolean solve() {
		solver.read(model);

		solver.solve();
		boolean feasible = solver.isFeasible();

		return feasible;
	}

	Object xor(int value, Object exp) { throw new RuntimeException("## Unsupported XOR "); }
	Object xor(Object exp, int value) { throw new RuntimeException("## Unsupported XOR"); }
	Object xor(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported XOR"); }

}
