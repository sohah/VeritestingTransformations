/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

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

import java.util.Map;

/**
 * @author Vaibhav Sharma (vaibhav@umn.edu)
 * Began with BinaryNonLinearIntegerExpression.java
 */
public class ComplexNonLinearIntegerExpression extends NonLinearIntegerExpression {
  public ComplexNonLinearIntegerExpression left;

  public Operator op;

  public Comparator cmprtr;

  public ComplexNonLinearIntegerExpression right;

  public IntegerExpression base;

  public ComplexNonLinearIntegerExpression() {
    left = right = null;
    op = Operator.NONE_OP;
    cmprtr = Comparator.NONE_CMP;
  }

  public ComplexNonLinearIntegerExpression(IntegerExpression l) {
    base = l;
    op = Operator.NONE_OP;
    cmprtr = Comparator.NONE_CMP;
    left = right = null;
  }

  public void initLR(IntegerExpression l, IntegerExpression r) {
    if(l instanceof ComplexNonLinearIntegerExpression) left = (ComplexNonLinearIntegerExpression) l;
    else left = new ComplexNonLinearIntegerExpression(l);
    if(r instanceof ComplexNonLinearIntegerExpression) right = (ComplexNonLinearIntegerExpression) r;
    else right = new ComplexNonLinearIntegerExpression(r);
  }

  public ComplexNonLinearIntegerExpression(IntegerExpression l, Operator o, IntegerExpression r) {
    initLR(l, r);
    op = o;
    cmprtr = Comparator.NONE_CMP;
  }

  public ComplexNonLinearIntegerExpression(IntegerExpression l, Comparator c, IntegerExpression r) {
    initLR(l, r);
    cmprtr = c;
    op = Operator.NONE_OP;
  }

  public ComplexNonLinearIntegerExpression(long l, Operator o, IntegerExpression r) {
    initLR(new IntegerConstant(l), r);
    op = o;
    cmprtr = Comparator.NONE_CMP;
  }

  public ComplexNonLinearIntegerExpression(long l, Comparator c, IntegerExpression r) {
    initLR(new IntegerConstant(l), r);
    cmprtr = c;
    op = Operator.NONE_OP;
  }

  public long solution() {
    long l = left.solution();
    if (op == Operator.NONE_OP && cmprtr == Comparator.NONE_CMP) return base.solution();
    long r = right.solution();
    if (op != Operator.NONE_OP && cmprtr == Comparator.NONE_CMP) {
      switch(op){
        case PLUS:       return l + r;
        case MINUS:      return l - r;
        case MUL: return l * r;
        case DIV: return l / r;
        case AND: return l & r;
        case OR: return l | r;
        case XOR: return l ^ r;
        case SHIFTL: return l << r;
        case SHIFTR: return l >> r;
        case SHIFTUR: return l >>> r;
        default: throw new RuntimeException("## Error: ComplexNonLinearSolution solution: l " + l + " op " + op + " r " + r);
      }
    } else if (cmprtr != Comparator.NONE_CMP && op == Operator.NONE_OP) {
      if(cmprtr.evaluate(l, r)) return l;
      else return r;
    }
    else { 
      throw new RuntimeException("## Error: ComplexNonLinearIntegerExpression with both op("+op.toString() + "), cmprtr("+cmprtr.toString()+") set\n");
    }
  }

  public void getVarsVals(Map<String,Object> varsVals) {
    left.getVarsVals(varsVals);
    right.getVarsVals(varsVals);
  }

  public String stringPC() {
    if(op == Operator.NONE_OP && cmprtr == Comparator.NONE_CMP) return base.stringPC();
    if(op == Operator.NONE_OP)  
      return "(" + left.stringPC() + cmprtr.toString() + right.stringPC() + ")";
    else 
      return "(" + left.stringPC() + op.toString() + right.stringPC() + ")";
  }

  public String toString() {
    if(op == Operator.NONE_OP && cmprtr == Comparator.NONE_CMP) return base.toString();
    if(op == Operator.NONE_OP)  
      return "(" + left.toString() + cmprtr.toString() + right.toString() + ")";
    else 
      return "(" + left.toString() + op.toString() + right.toString() + ")";
  }

  // JacoGeldenhuys
  @Override
  public void accept(ConstraintExpressionVisitor visitor) {
    visitor.preVisit(this);
    left.accept(visitor);
    right.accept(visitor);
    visitor.postVisit(this);
  }

  @Override
  public int compareTo(Expression expr) {
    if (expr instanceof ComplexNonLinearIntegerExpression) {
      ComplexNonLinearIntegerExpression e = (ComplexNonLinearIntegerExpression) expr;
      int r = -1;
      if(e.op == Operator.NONE_OP && op == Operator.NONE_OP)
        if(e.cmprtr == Comparator.NONE_CMP && cmprtr == Comparator.NONE_CMP)
          base._cmp(e.base); // use left if no operators used 
        else 
          r = cmprtr.compareTo(e.cmprtr);
      else r = op.compareTo(e.op);
      if (r == 0) {
        r = left.compareTo(e.left);
      }
      if (r == 0) {
        r = right.compareTo(e.right);
      }
      return r;
    } else {
      return getClass().getCanonicalName().compareTo(expr.getClass().getCanonicalName());
    }
  }

}
