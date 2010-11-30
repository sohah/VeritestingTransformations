package gov.nasa.jpf.symbc.concolic;

import gov.nasa.jpf.symbc.SymbolicInstructionFactory;
import gov.nasa.jpf.symbc.numeric.*;

public class PCAnalyzer {

	// this one will hold the parts that are easy to solve
	PathCondition simplePC;
	// this is the part that contains functions/operations
	// that we cannot solve with our DPs and hence want to use
	// concrete values on
	PathCondition concolicPC;

	/*
	 * Walks the PC and splits it into simplePC and concolicPC
	 */
	public void splitPathCondition(PathCondition pc) {
		PathCondition newPC = pc.make_copy();
		Constraint cRef = newPC.header;
		simplePC = new PathCondition();
		concolicPC = new PathCondition();

		while (cRef != null) {
			if (cRef instanceof RealConstraint) {
				// this will be the only one that goes to concolicPC for now
				concolicPC.prependUnlessRepeated(new RealConstraint((RealConstraint)cRef));
			} else if (cRef instanceof LinearIntegerConstraint) {
				simplePC.prependUnlessRepeated(new LinearIntegerConstraint((LinearIntegerConstraint)cRef));
			} else if (cRef instanceof MixedConstraint) {
				simplePC.prependUnlessRepeated(new MixedConstraint((MixedConstraint)cRef));
			} else if (cRef instanceof LogicalORLinearIntegerConstraints) {
				simplePC.prependUnlessRepeated(new LogicalORLinearIntegerConstraints(((LogicalORLinearIntegerConstraints)cRef).getList()));
			} else if (cRef instanceof NonLinearIntegerConstraint){
				concolicPC.prependUnlessRepeated(new NonLinearIntegerConstraint((NonLinearIntegerConstraint)cRef));
			} else	{
				throw new RuntimeException("## Error: Constraint not handled " + cRef);
			}
			cRef = cRef.and;
		}
		if (SymbolicInstructionFactory.debugMode) {
			System.out.println("--------begin after splitting------------");
			System.out.println("originalPC " + pc);
			System.out.println("concolicPC " + concolicPC);
			System.out.println("simplePC " + simplePC);
			System.out.println("--------end after splitting------------");
		}
	}

	PathCondition extraPC; // spaghetti code; TODO this better

	// for now assume only real expressions
	Constraint eqConcolicConstraint(Expression eRef) {
		if(eRef instanceof MathRealExpression) {
			MathFunction funRef;
			RealExpression	e_arg1Ref;
			RealExpression	e_arg2Ref;

			funRef = ((MathRealExpression)eRef).op;
			e_arg1Ref = ((MathRealExpression)eRef).arg1;
			e_arg2Ref = ((MathRealExpression)eRef).arg2;

			switch(funRef){
			case SIN:
			case COS:
			case ROUND:
			case EXP:
			case ASIN:
			case ACOS:
			case ATAN:
			case LOG:
			case TAN:
			case SQRT:return new RealConstraint(e_arg1Ref, Comparator.EQ, new RealConstant(e_arg1Ref.solution()));
			case POW:
			case ATAN2: {
				RealConstraint c1 = new RealConstraint(e_arg1Ref, Comparator.EQ, new RealConstant(e_arg1Ref.solution()));
				RealConstraint c2 = new RealConstraint(e_arg2Ref, Comparator.EQ, new RealConstant(e_arg2Ref.solution()));
				c1.and = c2;
				return c1;
			}
			default:
				throw new RuntimeException("## Error: Expression " + eRef);
			}
		}
		else if (eRef instanceof FunctionExpression) {
			Expression [] sym_args = ((FunctionExpression)eRef).sym_args;
			assert(sym_args != null && sym_args.length > 0);
			RealExpression e = (RealExpression)sym_args[0];// for now assume only real expressions; TODO the integer expressions
			RealConstraint c = new RealConstraint(e, Comparator.EQ, new RealConstant(e.solution()));
			for(int i=1; i<sym_args.length; i++) {
					RealExpression e2 = (RealExpression)sym_args[i];
					RealConstraint c2 = new RealConstraint(e2, Comparator.EQ, new RealConstant(e2.solution()));
					c2.and = c;
					c = c2;
			}
			return c;
		}
		else if (eRef instanceof BinaryNonLinearIntegerExpression) {

			IntegerExpression	e_arg1Ref;
			IntegerExpression	e_arg2Ref;

			e_arg1Ref = ((BinaryNonLinearIntegerExpression)eRef).left;
			e_arg2Ref = ((BinaryNonLinearIntegerExpression)eRef).right;
			LinearIntegerConstraint c1 = new LinearIntegerConstraint(e_arg1Ref, Comparator.EQ, new IntegerConstant(e_arg1Ref.solution()));
			LinearIntegerConstraint c2 = new LinearIntegerConstraint(e_arg2Ref, Comparator.EQ, new IntegerConstant(e_arg2Ref.solution()));
			c1.and = c2;
			return c1;
		}
		throw new RuntimeException("## Error: Expression " + eRef);
	}



	Expression getExpression(Expression eRef) {
		assert eRef != null;
		assert !(eRef instanceof RealConstant);

		if (eRef instanceof SymbolicReal || eRef instanceof RealConstant) {
			return eRef;
		}
		if (eRef instanceof SymbolicInteger || eRef instanceof IntegerConstant) {
			return eRef;
		}

		if(eRef instanceof BinaryRealExpression) {
			Operator    opRef = ((BinaryRealExpression)eRef).getOp();
			RealExpression	e_leftRef = ((BinaryRealExpression)eRef).getLeft();
			RealExpression	e_rightRef = ((BinaryRealExpression)eRef).getRight();

			return new BinaryRealExpression((RealExpression)getExpression(e_leftRef),opRef,(RealExpression)getExpression(e_rightRef));
		}


		if(eRef instanceof MathRealExpression || eRef instanceof FunctionExpression) {
			extraPC.prependUnlessRepeated(eqConcolicConstraint(eRef));
			return new RealConstant(((RealExpression)eRef).solution());
		}

		if(eRef instanceof BinaryNonLinearIntegerExpression) {
			extraPC.prependUnlessRepeated(eqConcolicConstraint(eRef));
			return new IntegerConstant(((BinaryNonLinearIntegerExpression)eRef).solution());
		}

		throw new RuntimeException("## Error: Expression " + eRef);
	}


//	RealConstraint traverseRealConstraint(RealConstraint cRef) {
//		Comparator c_compRef = cRef.getComparator();
//		RealExpression c_leftRef = (RealExpression)cRef.getLeft();
//		RealExpression c_rightRef = (RealExpression)cRef.getRight();
//
//		return new RealConstraint(getExpression(c_leftRef),c_compRef,getExpression(c_rightRef));
//	}
	Constraint traverseConstraint(Constraint cRef) {
		Comparator c_compRef = cRef.getComparator();
		Expression c_leftRef = cRef.getLeft();
		Expression c_rightRef = cRef.getRight();

		//return new Constraint(getExpression(c_leftRef),c_compRef,getExpression(c_rightRef));
		if(cRef instanceof RealConstraint)
			return new RealConstraint((RealExpression)(getExpression(c_leftRef)),c_compRef,(RealExpression)(getExpression(c_rightRef)));
		if(cRef instanceof NonLinearIntegerConstraint)
			return new LinearIntegerConstraint((IntegerExpression)(getExpression(c_leftRef)),c_compRef,(IntegerExpression)(getExpression(c_rightRef)));
		throw new RuntimeException("## Error: Constraint " + cRef);


	}
	public boolean solveSplitPC() {
		// first solve the simplePC and then use the results to update concolicPC
		if (simplePC.solve() == false) return false;
		if (SymbolicInstructionFactory.debugMode) {
			System.out.println("........................START SOLVING");
			System.out.println("--------------------");
			System.out.println("simplePC " + simplePC);
			System.out.println("--------------------");
		}

		// now replace all math functions in concolicPC
		// with their execution results with simplePC arguments

		//PathCondition simplifiedPC = new PathCondition();
		Constraint cRef = concolicPC.header;

		extraPC = new PathCondition();
		while (cRef != null) {
			simplePC.prependUnlessRepeated(traverseConstraint(cRef));
			cRef = (RealConstraint)cRef.and;
		}
		if(SymbolicInstructionFactory.debugMode) System.out.println("new PC " + simplePC);
		if(extraPC.header!=null) {
			if(SymbolicInstructionFactory.debugMode) System.out.println("extraPC constraints" + extraPC);
			simplePC.prependAllConjuncts(extraPC.header);
		}

		if(SymbolicInstructionFactory.debugMode){
			if (true /*SymbolicInstructionFactory.debugMode*/) {
				System.out.println("--------------------");
				System.out.println("before solving combined PC " + simplePC);
				System.out.println("--------------------");
			}

		simplePC.flagSolved = false;
		if(simplePC.solve())
			System.out.println("combined PC satisfiable");
		else
			System.out.println("combined PC not satisfiable");
//		if (true /*SymbolicInstructionFactory.debugMode*/) {
//			System.out.println("--------------------");
//			System.out.println("simplifiedPC " + simplePC);
//			System.out.println("--------------------");
//		}
		}
        return true;
	}

	public PathCondition getSimplifiedPC() {
		return simplePC;
	}


}
