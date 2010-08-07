package gov.nasa.jpf.symbc.numeric;

import java.util.HashMap;
import java.util.Map;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;

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

public class ProblemChoco2Coral extends ProblemGeneral {

	//Choco2 variables
	private CPSolver solver;
	private Model model;
	
	//Coral variables
	private static final long timeout = -1; //Config.timeout; // 1s default
	SolverKind solverKind = SolverKind.PSO_OPT4J;
	coral.PC pc = new coral.PC();
	Map<String, SymLiteral> variables = new HashMap<String, SymLiteral>();
	Map<SymLiteral, Range> ranges = new HashMap<SymLiteral, Range>(); 
		
	public ProblemChoco2Coral() {
		model = new CPModel();
		solver = new CPSolver();	
	}
		
	//Coral!
	
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
	Object eq(double value, Object exp) {
		return Util.eq(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object eq(Object exp, double value) {
		return Util.eq((SymDouble)exp, Util.createConstant(value));
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
	Object leq(double value, Object exp) {
		return Util.le(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object leq(Object exp, double value) {
		return Util.le((SymDouble)exp, Util.createConstant(value));
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
	Object lt(double value, Object exp) {
		return Util.lt(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object lt(Object exp, double value) {
		return Util.lt((SymDouble)exp, Util.createConstant(value));
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
	Object plus(double value, Object exp) {
		return Util.add(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object plus(Object exp, double value) {
		return Util.add((SymDouble)exp, Util.createConstant(value));
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
	Object mult(double value, Object exp) {
		return Util.mul(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object mult(Object exp, double value) {
		return Util.mul((SymDouble)exp, Util.createConstant(value));
	}
	
	@Override
	Object div(double value, Object exp) {
		return Util.div(Util.createConstant(value), (SymDouble)exp);
	}

	@Override
	Object div(Object exp, double value) {
		return Util.div((SymDouble)exp, Util.createConstant(value));
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
	
	//Choco2 w/ merges from Coral!
	
	Object div(int value, Object exp) { return Choco.div(value, (IntegerExpressionVariable) exp); }
	Object div(Object exp, int value) { return Choco.div((IntegerExpressionVariable) exp, value); }
	Object div(Object exp1, Object exp2) {
		if (exp1 instanceof IntegerExpressionVariable) {		
			return Choco.div((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); }
		else {
			if (exp1 instanceof SymDouble) {
				return Util.div((SymDouble)exp1, (SymDouble)exp2);
			} else if (exp1 instanceof SymInt) {
				return Util.div((SymInt)exp1, (SymInt)exp2);
			} else {
				throw new UnsupportedOperationException();
			}
		}
	}
	
	Object eq(int value, Object exp) { return Choco.eq(value, (IntegerExpressionVariable) exp);	}
	Object eq(Object exp, int value) { return Choco.eq((IntegerExpressionVariable) exp, value);	}
	Object eq(Object exp1, Object exp2) {
		if (exp1 instanceof IntegerExpressionVariable) {
			return Choco.eq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp1);	
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.eq((SymDouble)exp1, (SymDouble)exp2);	
			} else if (exp1 instanceof SymInt) {
				return Util.eq((SymInt)exp1, (SymInt)exp2);	
			} else {
				throw new UnsupportedOperationException();	
			}
		}
	}
		

	Object geq(int value, Object exp) { return Choco.geq(value, (IntegerExpressionVariable) exp);	}
	Object geq(Object exp, int value) { return Choco.geq((IntegerExpressionVariable) exp, value);	}
	Object geq(Object exp1, Object exp2) { 
		if (exp1 instanceof IntegerExpressionVariable) {			
			return Choco.geq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp1);
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.ge((SymDouble)exp1, (SymDouble)exp2);	
			} else if (exp1 instanceof SymInt) {
				return Util.ge((SymInt)exp1, (SymInt)exp2);	
			} else {
				throw new UnsupportedOperationException();	
			}
		}
	}


	int getIntValue(Object dpVar) {
		return solver.getVar((IntegerVariable) dpVar).getVal();		
	}
	
	Object gt(int value, Object exp) { return Choco.gt(value, (IntegerExpressionVariable) exp); }
	Object gt(Object exp, int value) { return Choco.gt((IntegerExpressionVariable) exp, value); }
	Object gt(Object exp1, Object exp2) { 
		if (exp1 instanceof IntegerExpressionVariable) {
			return Choco.gt((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.gt((SymDouble)exp1, (SymDouble)exp2);
			} else if (exp1 instanceof SymInt) {
				return Util.gt((SymInt)exp1, (SymInt)exp2);
			} else {
				throw new UnsupportedOperationException();
			}
		}
	}

	Object leq(int value, Object exp) { return Choco.leq(value, (IntegerExpressionVariable) exp); }
	Object leq(Object exp, int value) { return Choco.leq((IntegerExpressionVariable) exp, value); }
	Object leq(Object exp1, Object exp2) { 
		if (exp1 instanceof IntegerExpressionVariable) {
			return Choco.leq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.le((SymDouble)exp1, (SymDouble)exp2);	
			} else if (exp1 instanceof SymInt) {
				return Util.le((SymInt)exp1, (SymInt)exp2);	
			} else {
				throw new UnsupportedOperationException();	
			}
		}
	}

	Object lt(int value, Object exp) { return Choco.lt(value, (IntegerExpressionVariable) exp); }
	Object lt(Object exp, int value) { return Choco.lt((IntegerExpressionVariable) exp, value); }
	Object lt(Object exp1, Object exp2) { 
		if (exp1 instanceof IntegerExpressionVariable) {
			return Choco.lt((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.lt((SymDouble)exp1, (SymDouble)exp2);	
			} if (exp1 instanceof SymInt) {
				return Util.lt((SymInt)exp1, (SymInt)exp2);	
			} else {
				throw new UnsupportedOperationException();	
			}
		}
	}

	Object makeIntVar(String name, int min, int max) {
		return Choco.makeIntVar(name, min, max);
	}
	Object minus(int value, Object exp) { return Choco.minus(value, (IntegerExpressionVariable) exp); }
	Object minus(Object exp, int value) { return Choco.minus((IntegerExpressionVariable) exp, value); }
	Object minus(Object exp1, Object exp2)  { 
		if (exp1 instanceof IntegerExpressionVariable) { 
			return Choco.minus((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.sub((SymDouble)exp1, (SymDouble)exp2);
			} else if (exp1 instanceof SymInt) {
				return Util.sub((SymInt)exp1, (SymInt)exp2);
			} else {
				throw new UnsupportedOperationException();	
			}
		}
	}

	Object mult(int value, Object exp) { return Choco.mult(value, (IntegerExpressionVariable) exp); }
	Object mult(Object exp, int value) { return Choco.mult((IntegerExpressionVariable) exp, value); }
	Object mult(Object exp1, Object exp2)  { 
		if (exp1 instanceof IntegerExpressionVariable) { 
			return Choco.mult((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.mul((SymDouble)exp1, (SymDouble)exp2);			
			} else if (exp1 instanceof SymInt) {
				return Util.mul((SymInt)exp1, (SymInt)exp2);			
			} else {
				throw new UnsupportedOperationException();	
			}
		}
	}

	Object neq(int value, Object exp) { return Choco.neq(value, (IntegerExpressionVariable) exp); }
	Object neq(Object exp, int value) { return Choco.neq((IntegerExpressionVariable) exp, value); }
	Object neq(Object exp1, Object exp2)  { 
		if (exp1 instanceof IntegerExpressionVariable) { 
			return Choco.neq((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.ne((SymDouble)exp1, (SymDouble)exp2);	
			} else if (exp1 instanceof SymInt) {
				return Util.ne((SymInt)exp1, (SymInt)exp2);
			} else {
				throw new UnsupportedOperationException();
			}
		}
	}
	
	Object plus(int value, Object exp) { return Choco.plus(value, (IntegerExpressionVariable) exp); }
	Object plus(Object exp, int value) { return Choco.plus((IntegerExpressionVariable) exp, value); }
	Object plus(Object exp1, Object exp2)  { 
		if (exp1 instanceof IntegerExpressionVariable) {
			return Choco.plus((IntegerExpressionVariable) exp1, (IntegerExpressionVariable) exp2); 
		} else {
			if (exp1 instanceof SymDouble) {
				return Util.add((SymDouble)exp1, (SymDouble)exp2);
			} else if (exp1 instanceof SymInt) {
				return Util.add((SymInt)exp1, (SymInt)exp2);
			} else {
				throw new UnsupportedOperationException();
			}
		}
	}

	/*
	 *  Here we must be aware of both solvers.	
	 */
	@Override
	/**
	 * JPF calls this method to add a new boolean expression
	 * to the path condition 
	 */
	void post(Object constraint) {
		if (constraint instanceof SymBool) {
			pc.addConstraint((SymBool)constraint);
		} else {
			model.addConstraint((Constraint) constraint);	
		}
	}	

	private static int chocoCount = 0;
	private static int coralCount = 0;
	Env sol = null;
	/**
	 * JPF calls this method when it needs to solve the path condition
	 */		
	Boolean solve() {
		solver = new CPSolver();
		solver.read(model);
		
		solver.solve();
		boolean feasible = solver.isFeasible();		
		model = new CPModel();
		System.out.println(chocoCount + " : " + coralCount);
		chocoCount++;
		
		if (feasible) {
			coralCount++;
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
				//System.out.printf(">>> %s %s %s\n", pc.toString(), sol, result);
			}
		
			return result;		
		} else {
			return false;
		}
	}

	@SuppressWarnings("unused")
	private Env solveIt(final PC pc, final Solver solver) throws InterruptedException {
		final Env[] env = new Env[1];
		Config.nIterationsPSO = 4000;
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
		if (timeout > 0) {
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

	//Unimplemented methods
	
	Object and(int value, Object exp) {	throw new RuntimeException("## Unsupported and "); }
	Object and(Object exp, int value) {	throw new RuntimeException("## Unsupported and "); }
	Object and(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported and "); }

	Object mixed(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported mixed "); }

	Object or(int value, Object exp) {	throw new RuntimeException("## Unsupported OR "); }
	Object or(Object exp, int value) {	throw new RuntimeException("## Unsupported OR "); }
	Object or(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported OR "); }	

	Object shiftL(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftL"); }
	Object shiftL(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftL"); }
	Object shiftL(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftL"); }

	Object shiftR(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftR"); }
	Object shiftR(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftR"); }
	Object shiftR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftR"); } 	
	
	Object shiftUR(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftUR"); }
	Object shiftUR(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftUR"); }
	Object shiftUR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftUR"); }


	Object xor(int value, Object exp) { throw new RuntimeException("## Unsupported XOR "); }
	Object xor(Object exp, int value) { throw new RuntimeException("## Unsupported XOR"); }
	Object xor(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported XOR"); }
	
}
