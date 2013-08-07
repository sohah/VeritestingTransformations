//
// Copyright (C) 2006 United States Government as represented by the
// Administrator of the National Aeronautics and Space Administration
// (NASA).  All Rights Reserved.
//
// This software is distributed under the NASA Open Source Agreement
// (NOSA), version 1.3.  The NOSA has been approved by the Open Source
// Initiative.  See the file NOSA-1.3-JPF at the top of the distribution
// directory tree for the complete NOSA document.
//
// THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY
// KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
// LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
// SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT
// THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT
// DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE.
//
package gov.nasa.jpf.symbc.bytecode;

import gov.nasa.jpf.symbc.numeric.Comparator;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;

/**
 * Compare float ..., value1, value2 => ..., result
 */
public class FCMPG extends gov.nasa.jpf.jvm.bytecode.FCMPG {

    @Override
	public Instruction execute(ThreadInfo th) {
		StackFrame sf = th.getModifiableTopFrame();

		RealExpression sym_v1 = (RealExpression) sf.getOperandAttr(0);
		RealExpression sym_v2 = (RealExpression) sf.getOperandAttr(1);

		if (sym_v1 == null && sym_v2 == null) { // both conditions are concrete
			return super.execute( th);
		} else { // at least one condition is symbolic
			ChoiceGenerator<?> cg;
			int conditionValue;

			if (!th.isFirstStepInsn()) { // first time around
				cg = new PCChoiceGenerator(3);
				((PCChoiceGenerator)cg).setOffset(this.position);
				((PCChoiceGenerator)cg).setMethodName(this.getMethodInfo().getFullName());
				th.getVM().getSystemState().setNextChoiceGenerator(cg);
				return this;
			} else { // this is what really returns results
				cg = th.getVM().getSystemState().getChoiceGenerator();
				assert (cg instanceof PCChoiceGenerator) : "expected PCChoiceGenerator, got: " + cg;
				conditionValue = ((PCChoiceGenerator) cg).getNextChoice() - 1;
			}

			float v1 = Types.intToFloat(sf.pop());
			float v2 = Types.intToFloat(sf.pop());

			PathCondition pc;

			ChoiceGenerator<?> prev_cg = cg.getPreviousChoiceGeneratorOfType(PCChoiceGenerator.class);

			if (prev_cg == null)
				pc = new PathCondition();
			else
				pc = ((PCChoiceGenerator) prev_cg).getCurrentPC();
			assert pc != null;

			if (conditionValue == -1) {
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(Comparator.LT, sym_v2, sym_v1);
					} else
						pc._addDet(Comparator.LT, v2, sym_v1);
				} else
					pc._addDet(Comparator.LT, sym_v2, v1);

				if (!pc.simplify()) {// not satisfiable
					th.getVM().getSystemState().setIgnored(true);
				} else {
					((PCChoiceGenerator) cg).setCurrentPC(pc);
				}
			} else if (conditionValue == 0) {
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(Comparator.EQ, sym_v1, sym_v2);
					} else
						pc._addDet(Comparator.EQ, sym_v1, v2);
				} else
					pc._addDet(Comparator.EQ, v1, sym_v2);
				if (!pc.simplify()) {// not satisfiable
					th.getVM().getSystemState().setIgnored(true);
				} else {
					((PCChoiceGenerator) cg).setCurrentPC(pc);
				}
			} else { // 1
				if (sym_v1 != null) {
					if (sym_v2 != null) { // both are symbolic values
						pc._addDet(Comparator.GT, sym_v2, sym_v1);
					} else
						pc._addDet(Comparator.GT, v2, sym_v1);
				} else
					pc._addDet(Comparator.GT, sym_v2, v1);
				if (!pc.simplify()) {// not satisfiable
					th.getVM().getSystemState().setIgnored(true);
				} else {
					((PCChoiceGenerator) cg).setCurrentPC(pc);
				}
			}

			sf.push(conditionValue, false);
			return getNext(th);
		}
	}
}
