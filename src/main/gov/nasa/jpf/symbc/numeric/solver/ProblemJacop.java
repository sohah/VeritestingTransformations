package gov.nasa.jpf.symbc.numeric.solver;

import java.util.ArrayList;

import JaCoP.constraints.*;
import JaCoP.core.BooleanVariable;
import JaCoP.core.Store;
import JaCoP.core.Variable;
import JaCoP.search.DepthFirstSearch;
import JaCoP.search.IndomainMin;
import JaCoP.search.Search;
import JaCoP.search.SelectChoicePoint;
import JaCoP.search.SimpleSelect;
import JaCoP.search.SmallestDomain;
/**
 * Integration of the Choco CP library version 2 (2.1.1, specifically).
 * Currently only supports integer operations.
 *
 * @author staats
 *
 */

public class ProblemJacop extends ProblemGeneral {
	private Store store;	
	private int temp;
	ArrayList<Variable> vars;
	
	public ProblemJacop() {
		store = new Store();
		temp = 0;
		vars = new ArrayList<Variable>();
	}
	
	private Variable getIntTemp() {
		Variable v = new Variable(store, "int_tmp_" + String.valueOf(temp++), -100000, 100000);
		vars.add(v);
		return v;
	}
	
	private BooleanVariable getBooleanTemp() {
		BooleanVariable v = new BooleanVariable(store, "bool_tmp_" + String.valueOf(temp++));
		vars.add(v);
		return v;
	}
	
	private Variable getConstant(int value) {
		Variable v = new Variable(store, "const_" + String.valueOf(value) + "_" + String.valueOf(temp++), value, value);
		vars.add(v);
		return v;
	}
	
	private BooleanVariable addConstraint(PrimitiveConstraint pc) {		
		BooleanVariable t = getBooleanTemp();	
		Reified r = new Reified(pc, t);		
		store.impose(pc);
		store.impose(r);
		
		vars.add(t);
		return t;
	}
	
	public Object and(int value, Object exp) {	throw new RuntimeException("## Unsupported and "); }
	public Object and(Object exp, int value) {	throw new RuntimeException("## Unsupported and "); }
	public Object and(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported and "); }

	public Object div(int value, Object exp) {
		Variable z = getIntTemp();
		store.impose(new XdivYeqZ(getConstant(value), (Variable) exp, z));
		
		vars.add(z);
		return z;
	}
	public Object div(Object exp, int value) {
		Variable z = getIntTemp();
		store.impose(new XdivYeqZ((Variable) exp, getConstant(value), z));
		
		vars.add(z);
		return z;
	}
	public Object div(Object exp1, Object exp2) {
		Variable z = getIntTemp();
		store.impose(new XdivYeqZ((Variable) exp1, (Variable) exp2, z));
		
		vars.add(z);
		return z;
	}

	public Object div(double value, Object exp) {	throw new RuntimeException("## Unsupported double div "); }
	public Object div(Object exp, double value) {	throw new RuntimeException("## Unsupported double div "); }

	public Object eq(int value, Object exp) { 				
		PrimitiveConstraint c = new XeqC((Variable) exp, value);		
		return addConstraint(c);
	}
	public Object eq(Object exp, int value) { 
		PrimitiveConstraint c = new XeqC((Variable) exp, value);		
		return addConstraint(c);	
	}
	public Object eq(Object exp1, Object exp2) { 
		PrimitiveConstraint c = new XeqY((Variable) exp1, (Variable) exp2);		
		return addConstraint(c);	
	}

	public Object eq(double value, Object exp) {	throw new RuntimeException("## Unsupported eq "); }
	public Object eq(Object exp, double value) {	throw new RuntimeException("## Unsupported eq "); }

	public Object geq(int value, Object exp) { 
		PrimitiveConstraint c = new XlteqC((Variable) exp, value);		
		return addConstraint(c);	
	}
	public Object geq(Object exp, int value) { 
		PrimitiveConstraint c = new XgteqC((Variable) exp, value);		
		return addConstraint(c);		
	}
	public Object geq(Object exp1, Object exp2) { 
		PrimitiveConstraint c = new XgteqY((Variable) exp1, (Variable) exp2);		
		return addConstraint(c);		
	}

	public Object geq(double value, Object exp) {	throw new RuntimeException("## Unsupported geq "); }
	public Object geq(Object exp, double value) {	throw new RuntimeException("## Unsupported geq "); }

	public int getIntValue(Object dpVar) {
		return ((Variable) dpVar).value();
	}

	public double getRealValue(Object dpVar) {	throw new RuntimeException("## Unsupported get real value "); }
	public double getRealValueInf(Object dpvar) {	throw new RuntimeException("## Unsupported get real value "); }
	public double getRealValueSup(Object dpVar) {	throw new RuntimeException("## Unsupported get real value "); }

	public Object gt(int value, Object exp) {
		PrimitiveConstraint c = new XltC((Variable) exp, value);		
		return addConstraint(c);
	}
	public Object gt(Object exp, int value) { 
		PrimitiveConstraint c = new XgtC((Variable) exp, value);		
		return addConstraint(c);
	}
	public Object gt(Object exp1, Object exp2) {
		PrimitiveConstraint c = new XgtY((Variable) exp1, (Variable) exp2);		
		return addConstraint(c); 
	}

	public Object gt(double value, Object exp) {	throw new RuntimeException("## Unsupported double gt "); }
	public Object gt(Object exp, double value) {	throw new RuntimeException("## Unsupported double gt "); }

	public Object leq(int value, Object exp) { 
		PrimitiveConstraint c = new XgteqC((Variable) exp, value);		
		return addConstraint(c);  
	}
	public Object leq(Object exp, int value) { 
		PrimitiveConstraint c = new XlteqC((Variable) exp, value);		
		return addConstraint(c); 
	}
	public Object leq(Object exp1, Object exp2) {
		PrimitiveConstraint c = new XlteqY((Variable) exp1, (Variable) exp2);		
		return addConstraint(c); 
	}

	public Object leq(double value, Object exp) {	throw new RuntimeException("## Unsupported double leq "); }
	public Object leq(Object exp, double value) {	throw new RuntimeException("## Unsupported double leq "); }

	public Object lt(int value, Object exp) { 
		PrimitiveConstraint c = new XgtC((Variable) exp, value);		
		return addConstraint(c); 
	}
	public Object lt(Object exp, int value) { 
		PrimitiveConstraint c = new XltC((Variable) exp, value);		
		return addConstraint(c);  
	}
	public Object lt(Object exp1, Object exp2) { 
		PrimitiveConstraint c = new XltY((Variable) exp1, (Variable) exp2);		
		return addConstraint(c); 
	}

	public Object lt(double value, Object exp) {	throw new RuntimeException("## Unsupported double lt "); }
	public Object lt(Object exp, double value) {	throw new RuntimeException("## Unsupported double lt "); }

	public Object makeIntVar(String name, int min, int max) {
		Variable v = new Variable(store, name, min, max);
		vars.add(v);
		return v;
	}

	public Object makeRealVar(String name, double min, double max) {	throw new RuntimeException("## Unsupported make real "); }

	/* No minus operation exists!
	 * value - exp = Z 
	 * =>
	 * Z + exp = value
	 */
	public Object minus(int value, Object exp) {
		Variable z = getIntTemp();
		store.impose(new XplusYeqC(z, (Variable) exp, value));	
		
		vars.add(z);
		return z; 
	}
	
	/* exp - value = Z
	 * =>
	 * Z + value = exp
	 */		
	public Object minus(Object exp, int value) { 
		Variable z = getIntTemp();
		store.impose(new XplusCeqZ(z, value, (Variable) exp));
		
		vars.add(z);
		return z;
	}
	
	/*
	 * exp1 - exp2 = Z
	 * =>
	 * Z + exp2 = exp1
	 */
	public Object minus(Object exp1, Object exp2)  { 
		Variable z = getIntTemp();
		store.impose(new XplusYeqZ(z, (Variable) exp2, (Variable) exp1));
		
		vars.add(z);
		return z;
	}

	public Object minus(double value, Object exp) {	throw new RuntimeException("## Unsupported double minus "); }
	public Object minus(Object exp, double value) {	throw new RuntimeException("## Unsupported double minus "); }
	public Object mixed(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported mixed "); }

	public Object mult(int value, Object exp) { 
		Variable z = getIntTemp();
		store.impose(new XmulCeqZ((Variable) exp, value, z));
		
		vars.add(z);
		return z;
	}
	public Object mult(Object exp, int value) { 
		return mult(value, exp);
	}
	public Object mult(Object exp1, Object exp2)  { 
		Variable z = getIntTemp();
		store.impose(new XmulYeqZ((Variable) exp1, (Variable) exp2, z));
		
		vars.add(z);
		return z;
	}

	public Object mult(double value, Object exp) {	throw new RuntimeException("## Unsupported double mult "); }
	public Object mult(Object exp, double value) {	throw new RuntimeException("## Unsupported double mult "); }

	public Object neq(int value, Object exp) { 
		PrimitiveConstraint c = new XneqC((Variable) exp, value);
		return addConstraint(c);
	}
	public Object neq(Object exp, int value) { 
		return neq(value, exp);
	}
	public Object neq(Object exp1, Object exp2)  { 
		PrimitiveConstraint c = new XneqY((Variable) exp1, (Variable) exp2);		
		return addConstraint(c); 
	}

	public Object neq(double value, Object exp) {	throw new RuntimeException("## Unsupported double NEQ "); }
	public Object neq(Object exp, double value) {	throw new RuntimeException("## Unsupported double NEQ "); }

	public Object or(int value, Object exp) {	throw new RuntimeException("## Unsupported OR "); }
	public Object or(Object exp, int value) {	throw new RuntimeException("## Unsupported OR "); }
	public Object or(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported OR "); }
	
	public Object plus(int value, Object exp) { 
		Variable z = getIntTemp();
		store.impose(new XplusCeqZ((Variable) exp, value, z));
		
		vars.add(z);
		return z; 
	}
	public Object plus(Object exp, int value) { 
		return plus(exp, value);
	}
	public Object plus(Object exp1, Object exp2)  {
		Variable z = getIntTemp();
		store.impose(new XplusYeqZ((Variable) exp1, (Variable) exp2, z));
		
		vars.add(z);
		return z;
	}

	public Object plus(double value, Object exp) {	throw new RuntimeException("## Unsupported double plus "); }
	public Object plus(Object exp, double value) {	throw new RuntimeException("## Unsupported double plus "); }

	/**
	 * Constraints are added during other operations, so this doesn't actually do anything.
	 */
	public void post(Object constraint) { }

	public Object shiftL(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftL"); }
	public Object shiftL(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftL"); }
	public Object shiftL(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftL"); }

	public Object shiftR(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftR"); }
	public Object shiftR(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftR"); }
	public Object shiftR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftR"); }

	public Object shiftUR(int value, Object exp) {	throw new RuntimeException("## Unsupported shiftUR"); }
	public Object shiftUR(Object exp, int value) {	throw new RuntimeException("## Unsupported shiftUR"); }
	public Object shiftUR(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported shiftUR"); }

	/*
	 * One potential issue is determining the best way to build constraints.
	 * Currently the model is reset after solving, and the solver
	 * is reset right before solving. Is this the best way to do this?
	 * We could alternatively pop constraints when backtracking,
	 * though this would require some changes to how ProblemGeneral
	 * is interfaced.
	 *
	 */
	public Boolean solve() {
		Variable[] vs = new Variable[vars.size()];
		vs = vars.toArray(vs);
		
		boolean consistent = store.consistency();		
		if (consistent) {
			Search label = new DepthFirstSearch();
			SelectChoicePoint select = new SimpleSelect(vs,
					new SmallestDomain(), new IndomainMin());
			boolean result = label.labeling(store, select);
			return result;
			/*if (result) {
				System.out.println("SATISIFIED!");
				for (Variable v : vars) {
					System.out.println(v.id + " "  +  v.value());
				}
			} else {
				System.out.println("NOT SATISIFIED!");
			}*/
		} else {
			//System.out.println("NOT CONSISTENT -- We're done");
		}
		return false;
	}

	public Object xor(int value, Object exp) { throw new RuntimeException("## Unsupported XOR "); }
	public Object xor(Object exp, int value) { throw new RuntimeException("## Unsupported XOR"); }
	public Object xor(Object exp1, Object exp2) {	throw new RuntimeException("## Unsupported XOR"); }

}
