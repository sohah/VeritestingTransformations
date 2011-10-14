package gov.nasa.jpf.symbc.probsym;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.Constraint;
import gov.nasa.jpf.symbc.numeric.LinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.MixedConstraint;
import gov.nasa.jpf.symbc.numeric.NonLinearIntegerConstraint;
import gov.nasa.jpf.symbc.numeric.RealConstraint;
import gov.nasa.jpf.symbc.numeric.PathCondition;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

public class DependencyCalc {
	/*
	 * Code for doing dependency simplification
	 */

	private LinkedList<String> getSymbolicVariables(Constraint c) {
		Map<String,Object> varMap = new HashMap<String,Object>();
		c.getLeft().getVarsVals(varMap);
		c.getRight().getVarsVals(varMap);
		LinkedList<String> result = new LinkedList<String>();
		for (String s : varMap.keySet()) {
			result.add(s);
			//System.out.println(s);
		}
		return result;
	}
	
	// calculates constraint to variables mapping
	private Map<Constraint,LinkedList<String>> getConstraintVariableMap(Constraint c) {
		if (c == null)
			return null;
		Map<Constraint,LinkedList<String>> m = new HashMap<Constraint,LinkedList<String>>();
		while (c != null) {
			LinkedList<String> l = getSymbolicVariables(c);		
			m.put(c, l);
			c = c.and;
		}
		return m;
	}
	
	private String printConstraint(Constraint c) {
		return c.getLeft().toString() + " " + c.getComparator().toString() + " " + c.getRight().toString();
	}
	
	private void printConstraintSet(HashSet<Constraint> s) {
		System.out.println("----start----");
		for (Constraint c : s) {
			System.out.println("-> " + printConstraint(c));
		}
		System.out.println("----end----");		
	} 
	
	
	public HashSet<Constraint> calcDependencies(PathCondition pc) {
		//System.out.println("PC = " + pc);
		//PathCondition pc = getPC(vm);
		if (pc.header == null) {
			//System.out.println("PC null");
			return null;
		}
		LinkedList<String> newVars = getSymbolicVariables(pc.header);
		// calculate constraint -> variable map
		Map<Constraint,LinkedList<String>> map = getConstraintVariableMap(pc.header);
		if (map == null)
			return null;
		// calculate variable -> constraint map
		Map<String, HashSet<Constraint>> varMap = new HashMap<String, HashSet<Constraint>>(); 
		for (Map.Entry<Constraint, LinkedList<String>> entry : map.entrySet()) {
			Constraint c = entry.getKey();
			LinkedList<String> consVars = entry.getValue();
			for (String s : consVars) {
				HashSet<Constraint> consList = varMap.get(s);
				if (consList == null) {
					consList = new HashSet<Constraint>();
				}
				consList.add(c);
				varMap.put(s, consList);
			}
		}
		// now we have the direct mapping of vars -> constraints
		// but we need the closure or indirect mappings as well
		// we will cycle through the mapping until we get to a fixpoint
		boolean done = false;
		while (!done) {
			done = true;
			for (Map.Entry<String, HashSet<Constraint>> entry : varMap.entrySet()) {
				String v = entry.getKey();
				HashSet<Constraint> tmpSet = new HashSet<Constraint>();
				int setSize = entry.getValue().size();
				for (Constraint c : entry.getValue()) {
					LinkedList<String> varList = map.get(c);
					for (String newVar : varList) {
						tmpSet.addAll(varMap.get(newVar));
					}
				}
				int newSize = tmpSet.size();
				done &= (newSize == setSize);
				if (DEBUG && done == false) {
					System.out.println("##########Found transitive constraints##########");
				}
				varMap.put(v, tmpSet);
			}		
		}
		
		HashSet<Constraint> finalConstraintSet = new HashSet<Constraint>();
		for (String s : newVars) {
			finalConstraintSet.addAll(varMap.get(s));
		}
		return finalConstraintSet;
	}

	private Constraint copyConstraint(Constraint cRef) {

		if (cRef instanceof LinearIntegerConstraint)
		  return new LinearIntegerConstraint((LinearIntegerConstraint)cRef);
		else if (cRef instanceof NonLinearIntegerConstraint)
		  return new NonLinearIntegerConstraint((NonLinearIntegerConstraint)cRef);
		else if (cRef instanceof RealConstraint)
		  return new RealConstraint((RealConstraint)cRef);
		else if (cRef instanceof MixedConstraint)
		  return new MixedConstraint((MixedConstraint)cRef);
		else { 
            System.out.println("Should never happen, missed a type in copyConstraint");
			return null;
		}		
	}
	
	boolean DEBUG = false;
	
	public PathCondition calcMinPC(PathCondition pc) {
		DEBUG = SymbolicInstructionFactory.debugMode;
		HashSet<Constraint> minConstraints = calcDependencies(pc);
		PathCondition minPC = new PathCondition();		  
		if (minConstraints != null && pc.count() != 0) {
			if (DEBUG) {
			  if (minConstraints.size() < pc.count())
		        System.out.println("Reduction = " + ((float)minConstraints.size())/((float)pc.count()) + " " + minConstraints.size() + " " + pc.count());
			}
		  for (Constraint c : minConstraints) {
			minPC.prependUnlessRepeated(copyConstraint(c));
			//minPC.prependUnlessRepeated(c);
		  }
		  return minPC;
		}
		else 
			return pc;
	}

}
