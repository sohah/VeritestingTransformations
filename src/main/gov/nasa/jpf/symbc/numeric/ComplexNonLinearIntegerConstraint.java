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

// Author: Vaibhav Sharma (vaibhav@umn.edu)
// Begun with LogicalORLinearIntegerConstraints

package gov.nasa.jpf.symbc.numeric;

public class ComplexNonLinearIntegerConstraint extends Constraint{
  
  private ComplexNonLinearIntegerExpression cnlie;
  public String comment;
  
  public ComplexNonLinearIntegerConstraint () {
    super (null, null, null);
    cnlie = null;
  }
  
  public ComplexNonLinearIntegerConstraint (ComplexNonLinearIntegerExpression _cnlie) {
    super (null, null, null);
    cnlie = _cnlie;
  }

  public Constraint copy() {
    return new ComplexNonLinearIntegerConstraint(cnlie);
  }
  
  
  public ComplexNonLinearIntegerExpression getCNLIE () {
    return cnlie;
  }
  
	@Override
	public Constraint not() {
		throw new UnsupportedOperationException("Not supported");
		//return null;
	}
  
  public String toString () {
    StringBuilder sb = new StringBuilder();
    sb.append (cnlie.toString());
    sb.append ("(" + comment + ")");
    if (and != null) {
      sb.append (" && \n");
      sb.append (and.stringPC());
    }
    return sb.toString();
  }
  
  public String stringPC () {
    return this.toString();
  }
  
  public boolean equals (Object o) {
    if (!(o instanceof ComplexNonLinearIntegerConstraint))
      return false;
    ComplexNonLinearIntegerConstraint other = (ComplexNonLinearIntegerConstraint) o;
    return other.getCNLIE().compareTo(cnlie) == 0;
  }
}
