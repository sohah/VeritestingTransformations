/*******************************************************************************
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

package gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.SSAInstructions;

import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInstructionFactory;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.util.intset.IntIterator;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.Var;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpression;
import gov.nasa.jpf.symbc.veritesting.VeritestingAST.Expressions.VeriExpressionVisitor;

/**
 * SSA instruction representing a switch statement.
 */
public class SSASwitchInstruction implements VeriExpression {
    private final int iindex;
    private final Var val;

    private final int defaultLabel;

    private final int[] casesAndLabels;

    /**
     * The labels in casesAndLabels represent <em>instruction indices</em> in the IR that each switch case branches to.
     */
    public SSASwitchInstruction(int iindex, Var val, int defaultLabel, int[] casesAndLabels) {
        this.iindex = iindex;
        this.val = val;
        this.defaultLabel = defaultLabel;
        this.casesAndLabels = casesAndLabels;
    }

    public Var getVal() {
        return val;
    }

    public int getIindex() {
        return iindex;
    }


    public int getTarget(int caseValue) {
        for (int i = 0; i < casesAndLabels.length; i += 2)
            if (caseValue == casesAndLabels[i])
                return casesAndLabels[i + 1];

        return defaultLabel;
    }

    public int getDefault() {
        return defaultLabel;
    }

    public int[] getCasesAndLabels() {
        return casesAndLabels;
    }

    public IntIterator iterateLabels() {
        return new IntIterator() {
            private int i = 0;

            @Override
            public boolean hasNext() {
                return i < casesAndLabels.length;
            }

            @Override
            public int next() {
                int v = casesAndLabels[i];
                i += 2;
                return v;
            }
        };
    }


    @Override
    public String toString() {
        StringBuffer result = new StringBuffer("switch ");
        result.append(val);
        result.append(" [");
        for (int i = 0; i < casesAndLabels.length - 1; i++) {
            result.append(casesAndLabels[i]);
            i++;
            result.append("->");
            result.append(casesAndLabels[i]);
            if (i < casesAndLabels.length - 2) {
                result.append(",");
            }
        }
        result.append("]");
        return result.toString();
    }

    @Override
    public void visit(VeriExpressionVisitor v) {
        v.visitSwitchInstruction(this);
    }
}
