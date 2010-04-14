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

import java.util.ArrayList;
import java.util.List;

import cvc3.Expr;
import cvc3.Rational;

public class ProblemCVC3BitVector extends ProblemCVC3 {

	Object makeBitVectorVar(String name, int N) {
		try {
			return vc.varExpr(name, vc.bitvecType(N));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3BitVec: Could not create a bitvector var" + e);
		}
	}
	
	Object and(int value, Object exp) {
		try {
			Rational val = new Rational(value, vc.embeddedManager());
			return vc.newBVAndExpr(vc.newBVConstExpr(val, 32), (Expr) exp); 
		} catch (Exception e) {
			throw new RuntimeException("## Error CVC3BitVector ");
		}	
	}

	Object and(Object exp, int value) {
		try {
			Rational val = new Rational(value, vc.embeddedManager());
			return vc.newBVAndExpr((Expr) exp, vc.newBVConstExpr(val, 32)); 
		} catch (Exception e) {
			throw new RuntimeException("## Error CVC3BitVector ");
		}
	}

	Object and(Object exp1, Object exp2) {
		try {
			return vc.newBVAndExpr((Expr) exp1,  (Expr) exp2);
		} catch (Exception e) {
			throw new RuntimeException("## Error CVC3BitVector ");
		}
	}

	

	@Override
	Object div(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object div(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object div(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object div(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object div(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object eq(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object eq(Object exp, int value) {
		try {
			Rational val = new Rational(value, vc.embeddedManager());
			return vc.eqExpr((Expr)exp, vc.newBVConstExpr(val, 32));
		} catch (Exception e) {
			throw new RuntimeException("## Error: CVC3 BitVector");
		}
	}

	@Override
	Object eq(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object eq(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object eq(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object geq(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object geq(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object geq(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object geq(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object geq(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	int getIntValue(Object dpVar) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	double getRealValue(Object dpVar) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	double getRealValueInf(Object dpvar) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	double getRealValueSup(Object dpVar) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	Object gt(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object gt(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object gt(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object gt(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object gt(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object leq(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object leq(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object leq(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object leq(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object leq(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object lt(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object lt(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object lt(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object lt(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object lt(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object makeIntVar(String name, int min, int max) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object makeRealVar(String name, double min, double max) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object minus(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object minus(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object minus(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object minus(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object minus(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object mixed(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object mult(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object mult(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object mult(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object mult(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object mult(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object neq(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object neq(Object exp, int value) {
		try {
			Rational val = new Rational(value, vc.embeddedManager());
			return vc.notExpr(vc.eqExpr((Expr) exp, vc.newBVConstExpr(val, 32)));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3BitVector");
		}
	}

	@Override
	Object neq(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object neq(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object neq(Object exp, double value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object plus(int value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object plus(Object exp, int value) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object plus(Object exp1, Object exp2) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object plus(double value, Object exp) {
		// TODO Auto-generated method stub
		throw new RuntimeException("bit vector");
	}

	@Override
	Object plus(Object exp, double value) {
		try{
			Rational val = new Rational(value, vc.embeddedManager());
			List<Expr> exprs = new ArrayList<Expr>();
			exprs.add((Expr) exp);
			exprs.add(vc.newBVConstExpr(val, 64));
			return vc.newBVPlusExpr(64, exprs);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("## Error CVC3: Exception caught in CVC3 JNI: \n" + e);
		}
	}

	
}