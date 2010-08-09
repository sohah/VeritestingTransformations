//
//Copyright (C) 2005 United States Government as represented by the
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

import java.util.HashMap;
import java.util.Map;

import symlib.SymBool;
import symlib.SymDouble;
import symlib.SymInt;
import symlib.SymLiteral;
import symlib.SymNumber;
import symlib.Util;
import coral.PC;
import coral.solvers.Env;
import coral.solvers.Result;
import coral.solvers.Solver;
import coral.solvers.SolverKind;
import coral.util.Config;
import coral.util.Range;

/**
 * Interface of SPF with the randomized solvers from CORAL
 * (http://pan.cin.ufpe.br/coral).
 *
 * Four kinds of methods in this implementation:
 *
 * (1) factory methods: create objects from the symbolic library of
 * CORAL to correspond to the symbolic expressions from JPF's symbolic
 * execution
 *
 * (2) post(): every time a constraint is created (i.e., a boolean
 * expression in the context of a branching decision) this method will
 * be called.
 *
 * (3) solve(): this is the actual call to the solver.
 *
 * (4) get*Value(): this method retrieves the solutions associated
 * with each variables if they exist.
 *
 *
 * @author damorim
 *
 */
public class ProblemCoral extends ProblemGeneral {

	private static final long timeout = -1; //Config.timeout; // 1s default
	SolverKind solverKind = SolverKind.PSO_OPT4J;
	coral.PC pc = new coral.PC();
	Map<String, SymLiteral> variables = new HashMap<String, SymLiteral>();
	Map<SymLiteral, Range> ranges = new HashMap<SymLiteral, Range>();

	//TODO: using min and max. try inferring value ranges...
	@Override
	Object makeIntVar(String name, int min, int max) {
		SymLiteral result = variables.get(name);
		if (result == null) {
			result = Util.createSymLiteral(0/*default value*/);
			variables.put(name, result);
			ranges.put(result, new Range(min, max));
		}
		return result;
	}

	@Override
	Object makeRealVar(String name, double min, double max) {
		SymLiteral result = variables.get(name);
		if (result == null) {
			result = Util.createSymLiteral(0d/*default value*/);
			variables.put(name, result);
			ranges.put(result, new Range((int)min, (int)max));
		}
		return result;
	}

	@Override
	Object eq(int value, Object exp) {
		return Util.eq(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object eq(Object exp, int value) {
		return Util.eq((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object eq(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.eq((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.eq((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object eq(double value, Object exp) {
		return Util.eq(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object eq(Object exp, double value) {
		return Util.eq((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object neq(int value, Object exp) {
		return Util.ne(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object neq(Object exp, int value) {
		return Util.ne((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object neq(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.ne((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.ne((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object neq(double value, Object exp) {
		return Util.ne(Util.createConstant(value),(SymDouble)exp);
	}

	@Override
	Object neq(Object exp, double value) {
		return Util.ne((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object leq(int value, Object exp) {
		return Util.le(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object leq(Object exp, int value) {
		return Util.le((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object leq(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.le((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.le((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object leq(double value, Object exp) {
		return Util.le(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object leq(Object exp, double value) {
		return Util.le((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object geq(int value, Object exp) {
		return Util.ge(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object geq(Object exp, int value) {
		return Util.ge((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object geq(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.ge((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.ge((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object geq(double value, Object exp) {
		return Util.ge(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object geq(Object exp, double value) {
		return Util.ge((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object lt(int value, Object exp) {
		return Util.lt(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object lt(Object exp, int value) {
		return Util.lt((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object lt(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.lt((SymDouble)exp1, (SymDouble)exp2);
		} if (exp1 instanceof SymInt) {
			return Util.lt((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object lt(double value, Object exp) {
		return Util.lt(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object lt(Object exp, double value) {
		return Util.lt((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object gt(int value, Object exp) {
		return Util.gt(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object gt(Object exp, int value) {
		return Util.gt((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object gt(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.gt((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.gt((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object gt(double value, Object exp) {
		return Util.gt(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object gt(Object exp, double value) {
		return Util.gt((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object plus(int value, Object exp) {
		return Util.add(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object plus(Object exp, int value) {
		return Util.add((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object plus(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.add((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.add((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object plus(double value, Object exp) {
		return Util.add(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object plus(Object exp, double value) {
		return Util.add((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object minus(int value, Object exp) {
		return Util.sub((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object minus(Object exp, int value) {
		return Util.sub(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object minus(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.sub((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.sub((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object minus(double value, Object exp) {
		return Util.sub((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object minus(Object exp, double value) {
		return Util.sub(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object mult(int value, Object exp) {
		return Util.mul(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object mult(Object exp, int value) {
		return Util.mul((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object mult(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.mul((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.mul((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object mult(double value, Object exp) {
		return Util.mul(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object mult(Object exp, double value) {
		return Util.mul((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object div(int value, Object exp) {
		return Util.div(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object div(Object exp, int value) {
		return Util.div((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object div(Object exp1, Object exp2) {
		if (exp1 instanceof SymDouble) {
			return Util.div((SymDouble)exp1, (SymDouble)exp2);
		} else if (exp1 instanceof SymInt) {
			return Util.div((SymInt)exp1, (SymInt)exp2);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	Object div(double value, Object exp) {
		return Util.div(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object div(Object exp, double value) {
		return Util.div((SymDouble)exp, Util.createConstant(value));
	}

	@Override
	Object and(int value, Object exp) {
		return Util.and(value==1?Util.TRUE:Util.FALSE, (SymBool)exp);
	}

	@Override
	Object and(Object exp, int value) {
		return Util.and((SymBool)exp, value==1?Util.TRUE:Util.FALSE);
	}

	@Override
	Object and(Object exp1, Object exp2) {
		return Util.and((SymBool)exp1, (SymBool)exp2);
	}

	@Override
	Object or(int value, Object exp) {
		return Util.or(value==1?Util.TRUE:Util.FALSE, (SymBool)exp);
	}

	@Override
	Object or(Object exp, int value) {
		return Util.or((SymBool)exp, value==1?Util.TRUE:Util.FALSE);
	}

	@Override
	Object or(Object exp1, Object exp2) {
		return Util.or((SymBool)exp1, (SymBool)exp2);
	}

	@Override
	Object xor(int value, Object exp) {
		return Util.xor(value==1?Util.TRUE:Util.FALSE, (SymBool)exp);
	}

	@Override
	Object xor(Object exp, int value) {
		return Util.xor((SymBool)exp, value==1?Util.TRUE:Util.FALSE);
	}

	@Override
	Object xor(Object exp1, Object exp2) {
		return Util.xor((SymBool)exp1, (SymBool)exp2);
	}

	@Override
	Object shiftL(int value, Object exp) {
		return Util.sl(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object shiftL(Object exp, int value) {
		return Util.sl((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object shiftL(Object exp1, Object exp2) {
		return Util.sl((SymInt)exp1, (SymInt)exp2);
	}

	@Override
	Object shiftR(int value, Object exp) {
		return Util.sr(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object shiftR(Object exp, int value) {
		return Util.sr((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object shiftR(Object exp1, Object exp2) {
		return Util.sr((SymInt)exp1, (SymInt)exp2);
	}

	@Override
	Object shiftUR(int value, Object exp) {
		return Util.usr(Util.createConstant(value), (SymInt)exp);
	}

	@Override
	Object shiftUR(Object exp, int value) {
		return Util.usr((SymInt)exp, Util.createConstant(value));
	}

	@Override
	Object shiftUR(Object exp1, Object exp2) {
		return Util.usr((SymInt)exp1, (SymInt)exp2);
	}

	@Override
	Object mixed(Object exp1, Object exp2) {
		throw new UnsupportedOperationException("WHAT IS IT?");
	}

	Object sin(Object exp) {
		return Util.sin((SymDouble)exp);
	}

	Object cos(Object exp) {
		return Util.cos((SymDouble)exp);
	}

	Object round(Object exp) {
		return Util.round((SymDouble)exp);
	}

	Object exp(Object exp) {
		return Util.exp((SymDouble)exp);
	}

	Object asin(Object exp) {
		return Util.asin((SymDouble)exp);
	}

	Object acos(Object exp) {
		return Util.acos((SymDouble)exp);
	}

	Object atan(Object exp) {
		return Util.atan((SymDouble)exp);
	}

	Object log(Object exp) {
		return Util.log((SymDouble)exp);
	}

	Object tan(Object exp) {
		return Util.tan((SymDouble)exp);
	}

	Object sqrt(Object exp) {
		return Util.sqrt((SymDouble)exp);
	}

	Object power(Object exp1, Object exp2) {
		return Util.pow((SymDouble)exp1, (SymDouble)exp2);
	}

	Object power(Object exp1, double exp2) {
		return Util.pow((SymDouble)exp1, Util.createConstant(exp2));
	}

	Object power(double exp1, Object exp2) {
		return Util.pow(Util.createConstant(exp1), (SymDouble)exp2);
	}

	Object atan2(Object exp1, Object exp2) {
		return Util.atan2((SymDouble)exp1, (SymDouble)exp2);
	}

	Object atan2(Object exp1, double exp2) {
		return Util.atan2((SymDouble)exp1, Util.createConstant(exp2));
	}

	Object atan2(double exp1, Object exp2) {
		return Util.atan2(Util.createConstant(exp1), (SymDouble)exp2);
	}

	Env sol = null;
	@Override
	/**
	 * JPF calls this method when it needs to solve the path condition
	 */
	Boolean solve() {
		Solver solver = solverKind.get();
		Boolean result = null;
		try {
			sol = solveIt(pc, solver);
			/**
			 * this is to comply with the assumption
			 * of the calling method
			 */
			if (sol.getResult() == Result.SAT) {
				result = true;
			}
		} catch (Exception _) {
		}
		finally {
//			System.out.printf(">>> %s %s %s\n", pc.toString(), sol, result);
		}
		return result;
	}



	@SuppressWarnings("unused")
	private Env solveIt(final PC pc, final Solver solver) throws InterruptedException {
		final Env[] env = new Env[1];
		Config.nIterationsPSO = 400; // number of iterations
		Runnable solverJob = new Runnable() {
			@Override
			public void run() {
				try {
					env[0] = solver.getCallable(pc).call();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		};

		if (timeout > 0) { // old code; not executed
			Thread t = new Thread(solverJob);
			t.start();
			t.join(timeout);
			solver.setPleaseStop(true);
			Thread.sleep(10);
		} else {
			solverJob.run();
		}
		return env[0];
	}

	@Override
	double getRealValueInf(Object dpvar) {
		return ranges.get((SymLiteral)dpvar).getLo();
	}

	@Override
	double getRealValueSup(Object dpVar) {
		return ranges.get((SymLiteral)dpVar).getHi();
	}

	@Override
	double getRealValue(Object dpVar) {
		SymNumber symNumber = sol.getValue((SymLiteral)dpVar);
		return symNumber.evalNumber().doubleValue();
	}

	@Override
	int getIntValue(Object dpVar) {
		SymNumber symNumber = sol.getValue((SymLiteral)dpVar);
		return symNumber.evalNumber().intValue();
	}

	@Override
	/**
	 * JPF calls this method to add a new boolean expression
	 * to the path condition
	 */
	void post(Object constraint) {
		pc.addConstraint((SymBool)constraint);
	}

}