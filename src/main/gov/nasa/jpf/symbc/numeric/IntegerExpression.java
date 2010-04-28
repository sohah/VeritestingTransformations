
//Copyright (C) 2005 United States Government as represented by the
//Administrator of the National Aeronautics and Space Administration
//(NASA).  All Rights Reserved.

//This software is distributed under the NASA Open Source Agreement
//(NOSA), version 1.3.  The NOSA has been approved by the Open Source
//Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
//directory tree for the complete NOSA document.

//THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
//KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
//LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
//SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
//A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
//THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
//DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.


package gov.nasa.jpf.symbc.numeric;

//import java.util.*;
import static gov.nasa.jpf.symbc.numeric.Operator.*;

public abstract class IntegerExpression extends Expression {

    //returns -1 if (this < i), 0 if equal and 1 otherwise 
    public IntegerExpression _cmp (long i) 
    {
        return new BinaryNonLinearIntegerExpression(this, CMP, new IntegerConstant((int)i));
    }

    public IntegerExpression _cmp_reverse (long i) 
    {
        return new BinaryNonLinearIntegerExpression(new IntegerConstant((int)i), CMP, this);
    }

    public IntegerExpression _cmp (IntegerExpression e) 
    {
        return new BinaryNonLinearIntegerExpression(this, CMP, e);
    }
    
//------------------------------------------------------
    
	public IntegerExpression _minus_reverse (int i) 
	{
		return new BinaryNonLinearIntegerExpression(new IntegerConstant(i), MINUS, this);
	}
	
	public IntegerExpression _minus (int i) 
	{
		//simplify
		if (i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, MINUS, new IntegerConstant(i));
	}

	public IntegerExpression _minus (IntegerExpression e) 
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 0)
				return this;
		}
		if (e == this)
			return new IntegerConstant(0);
		
		return new BinaryNonLinearIntegerExpression(this, MINUS, e);
	}

	public IntegerExpression _mul (int i) 
	{
		//simplify
		if (i == 1)
			return this;
		if (i == 0)
			return new IntegerConstant(0);
		
		return new BinaryNonLinearIntegerExpression(this, MUL, new IntegerConstant(i));
	}

	public IntegerExpression _mul (IntegerExpression e) 
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 1)
				return this;
			if (ic.value == 0)
				return new IntegerConstant(0);
		}

		return new BinaryNonLinearIntegerExpression(this, MUL, e);
	}

	public IntegerExpression _plus (int i) 
	{
		//simplify
		if (i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, PLUS, new IntegerConstant(i));
	}

	public IntegerExpression _plus (IntegerExpression e) 
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 0)
				return this;
		}
		
		return new BinaryNonLinearIntegerExpression(this, PLUS, e);
	}

	public IntegerExpression _shiftR(IntegerExpression i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftL(IntegerExpression i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftUR(IntegerExpression i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _and(IntegerExpression e)
	{
		//simplify
		if (e instanceof IntegerConstant) {
			IntegerConstant ic = (IntegerConstant)e;
			if (ic.value == 0)
				return new IntegerConstant(0);
		}
	
		return new BinaryNonLinearIntegerExpression(this, AND, e);
		
}

	public IntegerExpression _or(IntegerExpression i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftR(int i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftL(int i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftUR(int i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _and(int i)
	{
		if(i == 0) 
			return new IntegerConstant(0);
		return new BinaryNonLinearIntegerExpression(this, AND, new IntegerConstant((int)i));
	}

	public IntegerExpression _or(int i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _rem(int i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _rem(IntegerExpression i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _neg()
	{
		return new BinaryNonLinearIntegerExpression(new IntegerConstant(0), MINUS, this);
	}
	
	/*
	 * Additional support for longs so that we are not downcasting in the
	 * individual bytecodes
	 */
	public IntegerExpression _minus_reverse (long i) 
	{
		return new BinaryNonLinearIntegerExpression(new IntegerConstant((int)i), MINUS, this);
	}
	
	public IntegerExpression _minus (long i) 
	{
		//simplify
		if (i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, MINUS, new IntegerConstant((int)i));
	}

	public IntegerExpression _mul (long i) 
	{
		//simplify
		if (i == 1)
			return this;
		if (i == 0)
			return new IntegerConstant(0);

		return new BinaryNonLinearIntegerExpression(this, MUL, new IntegerConstant((int)i));
	}

	public IntegerExpression _plus (long i) 
	{
		//simplify
		if (i == 0)
			return this;
		return new BinaryNonLinearIntegerExpression(this, PLUS, new IntegerConstant((int)i));
	}

	public IntegerExpression _shiftR(long i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftL(long i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _shiftUR(long i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	public IntegerExpression _rem(long i)
	{
		throw new RuntimeException( "## Error: Operation not supported!" );
	}

	//TODO test this
	public int solution() {
		throw new RuntimeException( "## Error: Expression Solution request Error: " + this);
		//System.out.println("Expression Solution request Error: " + this);
		//return -666;
	}

}
